open Term
open Basic
open Parser
open Entry

let compose f g = fun x -> f (g x)
                   
let eprint lc fmt =
  Debug.(debug D_notice ("%a " ^^ fmt) pp_loc lc)

let mk_entry md e =
  match e with
  | Decl(lc,id,st,ty) ->
    begin
      eprint lc "Declaration of constant '%a'." pp_ident id;
      Env.declare lc id st ty;
      let cst = mk_name md id in
      Termination.add_constant cst st ty
    end
  | Def(lc,id,opaque,ty,te) ->
    begin
      let opaque_str = if opaque then " (opaque)" else "" in
      eprint lc "Definition of symbol '%a'%s." pp_ident id opaque_str;
      Env.define lc id opaque te ty;
      let cst = mk_name md id in
      begin
        match ty with
        | Some tt -> Termination.add_constant cst Definable tt
        | None    ->
           Termination.add_constant cst Definable (Env.infer te)
      end;
      let rul : Rule.untyped_rule = { name= Delta(cst) ;
                   ctx = [] ;
                   pat = Pattern(lc, cst, []);
                   rhs = te ;
                 }
      in Termination.add_rules [Rule.to_rule_infos rul]
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
      Termination.add_rules (List.map to_rule_infos rs)
    end
  | Eval(_,_,_)
  | Infer(_,_,_)
  | Check(_, _, _, _)
  | DTree(_, _, _)
  | Print(_, _)
  | Name(_, _) -> ()
  | Require(lc,md) ->
      Env.import lc md;
      Termination.import lc md

let run_on_file file=
  let input = open_in file in
  Debug.debug Signature.D_module "Processing file '%s'..." file;
  Termination.initialize ();
  let last_point =
    try String.rindex file '.'
    with Not_found -> 0
  in
  let ext = Str.string_after file last_point in
  if ext=".dk"
  then
    begin
      let md = Env.init file in
      Parser.handle_channel md (mk_entry md) input
    end
  else
    begin
      let md = mk_mident (Str.string_before file last_point) in
      List.iter (mk_entry md) (Tpdb_to_dk.load md file)
    end;
  let colored n s =
    if !Errors.color
    then "\027[3" ^ string_of_int n ^ "m" ^ s ^ "\027[m"
    else s
  in
  let green  = colored 2 in
  let orange = colored 3 in
  if Termination.termination_check ()
  then Format.eprintf "%s@." (green "YES")
  else Format.eprintf "%s@." (orange "MAYBE");
  close_in input

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
       | Env.DebugFlagNotRecognized 'p' ->
         Debug.enable_flag Positivity.D_positivity
    ) st

let _ =
  let run_on_stdin = ref None  in
  let options = Arg.align
    [ ( "-d"
      , Arg.String set_debug
      , "flags enables debugging for all given flags [xsgap] and [qnocutrm] inherited from Dedukti" )
    ; ( "-dkv"
      , Arg.Unit (fun () -> set_debug "montru")
      , " Verbose mode (equivalent to -d 'montru')" )
    ; ( "-v"
      , Arg.Unit (fun () -> set_debug "xsgap")
      , " Verbose mode (equivalent to -d 'wsgap')" )
    ; ( "-q"
      , Arg.Unit (fun () -> set_debug "q")
      , " Quiet mode (equivalent to -d 'q'" )
    ; ( "-nc"
      , Arg.Clear Errors.color
      , " Disable colors in the output" )
    ; ( "-stdin"
      , Arg.String (fun n -> run_on_stdin := Some(n))
      , "MOD Parses standard input using module name MOD" )]
  in
  let usage = "Usage: " ^ Sys.argv.(0) ^ " [OPTION]... [FILE]...\n" in
  let usage = usage ^ "Available options:" in
  let files =
    let files = ref [] in
    Arg.parse options (fun f -> files := f :: !files) usage;
    List.rev !files
  in
  try
    List.iter run_on_file files;
    match !run_on_stdin with
    | None   -> ()
    | Some m ->
      let md = Env.init m in
      Parser.handle_channel md (mk_entry md) stdin;
      Errors.success "Standard input was successfully checked.\n"
  with
  | Env.EnvError (l,e) -> Errors.fail_env_error l e
  | Sys_error err      -> Errors.fail_sys_error err
  | Exit               -> exit 3
