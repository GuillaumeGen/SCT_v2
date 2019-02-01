open Basic
open Entry
open Input
open Symbols
open Callgraph

let mk_dk_entry md e =
  let eprint lc fmt =
    Debug.(debug D_notice ("%a " ^^ fmt) pp_loc lc) in
  match e with
  | Decl(lc,id,st,ty) ->
    begin
      eprint lc "Declaration of constant '%a'." pp_ident id;
      Env.declare lc id st ty;
      let cst = Dk.string_of_name (mk_name md id) in
      DkRules.declare !graph cst ty;
    end
  | Def(lc,id,opaque,ty,te) ->
    begin
      let opaque_str = if opaque then " (opaque)" else "" in
      eprint lc "Definition of symbol '%a'%s." pp_ident id opaque_str;
      Env.define lc id opaque te ty;
      let cst = mk_name md id in
      begin
        match ty with
        | Some tt -> DkRules.declare !graph (Dk.string_of_name cst) tt
        | None    ->
          DkRules.declare !graph (Dk.string_of_name cst) (Env.infer te)
      end;
      DkRules.add_rule !graph (Delta cst) (Pattern (lc, cst, [])) te
    end
  | Rules(lc,rs) ->
    begin
      let open Rule in
      let get_infos p =
        match p with
        | Pattern(l,cst,_) -> (l,cst)
        | _                -> (dloc,mk_name (mk_mident "") dmark)
      in
      let r = List.hd rs in (* cannot fail. *)
      let (l,cst) = get_infos r.pat in
      eprint l "Adding rewrite rules for '%a'" pp_name cst;
      List.iter (fun (_,x) -> eprint (get_loc_pat r.pat) "%a" pp_typed_rule x)
          (Env.add_rules rs); 
      List.iter
        (fun (r : untyped_rule) -> DkRules.add_rule !graph r.name r.pat r.rhs)
        rs
    end
  | Eval(_,_,_)
  | Infer(_,_,_)
  | Check(_, _, _, _)
  | DTree(_, _, _)
  | Print(_, _)
  | Name(_, _) -> ()
  | Require(lc,md) -> DkRules.import lc md


let run_on_file file=
  Callgraph.initialize ();
  let input = open_in file in
  let (md,ext) =
    let last_point =
      begin
        try String.rindex file '.'
        with Not_found -> failwith "No file extension found"
      end
    in
    (Str.string_before file last_point, Str.string_after file last_point) in
  if ext = ".dk"
  then
    begin
      let md = Env.init file in
      Parser.Parse_channel.handle md (mk_dk_entry md) input
    end
  else if ext = ".xml"
  then
    begin
      let md2 = Env.init file in
      let dk_string = Tpdb_to_dk.load md2 file in
      if !(Tpdb_to_dk.export_dk_file)
      then 
        (let output = Format.formatter_of_out_channel (open_out (md^".dk")) in
        Format.fprintf output "%s@." dk_string);
      Parser.Parse_string.handle md2 (mk_dk_entry md2) dk_string
    end
  else failwith "Not handled file extension";
  close_in input;
  let colored n s =
    if !Errors.color
    then "\027[3" ^ string_of_int n ^ "m" ^ s ^ "\027[m"
    else s
  in
  let green  = colored 2 in
  let orange = colored 3 in
  let b,l = Sizechange.check_sct !Callgraph.graph in
  if Positivity.check_positivity !Callgraph.graph !Sizematrix.cstr && b
  then Format.eprintf "%s@." (green "YES")
  else
    begin
      let syms = !(!(Callgraph.graph).symbols) in
      List.iter
        (fun (_,i,ll) ->
          (IMap.find i syms).result <-
            SelfLooping ll :: (IMap.find i syms).result)
        l;
      Format.eprintf "%s@." (orange "MAYBE");
      let lc_result : Symbols.symbol -> unit =
        fun sy ->
          if sy.result = []
          then ()
          else
            List.iter
              (fun lc ->
                 Format.eprintf
                   "\027[31m * %s is %a relatively to the rules\027[m@."
                   sy.name
                   pp_local_result lc;
                   (match lc with
                    | SelfLooping l   ->
                      Format.eprintf "  - %a@."
                        (pp_list "\n  - " Format.pp_print_string) l
                    | DefinableType s ->
                      Format.eprintf "  - %a@."
                        Format.pp_print_string s
                    | NotPositive s   ->
                      Format.eprintf "  - %a@."
                        Format.pp_print_string s
                   )
              )
              sy.result in
      IMap.iter (fun k -> lc_result) !(!Callgraph.graph.symbols)
    end
             
           

let set_debug : string -> unit =
  fun st ->
    String.iter
    (fun c ->
       try Env.set_debug_mode (String.make 1 c)
       with
       | Env.DebugFlagNotRecognized 'x' ->
         Debug.enable_flag Sizematrix.D_matrix
       | Env.DebugFlagNotRecognized 's' ->
         Debug.enable_flag Sizechange.D_sctsummary
       | Env.DebugFlagNotRecognized 'g' ->
         Debug.enable_flag Callgraph.D_graph
       | Env.DebugFlagNotRecognized 'a' ->
         Debug.enable_flag Callgraph.D_call
    ) st
    
let _ =
  let options = Arg.align
     [( "-d"
      , Arg.String set_debug
      , "flags enables debugging for all given flags [xsgap] and [qnocutrm] inherited from Dedukti" ) ;
      ("--create-dk"
      , Arg.Set Tpdb_to_dk.export_dk_file
      , "create the dk file from an xml" ) ;
      ( "--dk-v"
      , Arg.Unit (fun () -> set_debug "montru")
      , " Verbose mode for Dedukti errors (equivalent to -d 'montru')" ) ;
      ( "--sz-v"
      , Arg.Unit (fun () -> set_debug "xsga")
      , " Verbose mode for SCT specific errors(equivalent to -d 'xsga')" ) ;
      ( "--verbose"
      , Arg.Unit (fun () -> set_debug "montruxsga")
      , " Most verbose mode (equivalent to -d 'montruxsga')" ) ;
      ( "-q"
      , Arg.Unit (fun () -> Env.set_debug_mode "q")
      , " Quiet mode (equivalent to -d 'q'" ) ;
      ( "-nc"
      , Arg.Clear Errors.color
      , " Disable colors in the output" )
     ]
  in
  let usage = "Usage: " ^ Sys.argv.(0) ^ " [OPTION]... [FILE]...\n" in
  let usage = usage ^ "Available options:" in
  let files =
    let files = ref [] in
    Arg.parse options (fun f -> files := f :: !files) usage;
    List.rev !files
  in
  List.iter run_on_file files
