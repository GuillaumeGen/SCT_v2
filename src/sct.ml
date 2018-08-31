open Term
open Basic
open Parser
open Entry

let eprint lc fmt =
  Debug.(debug d_notice ("%a " ^^ fmt) pp_loc lc)

let mk_entry md e =
  match e with
  | Decl(lc,id,st,ty) ->
    begin
      eprint lc "Declaration of constant '%a'." pp_ident id;
      let cst = mk_name md id in
      Termination.add_constant cst st ty
    end
  | Def(lc,id,opaque,ty,te) ->
    begin
      let opaque_str = if opaque then " (opaque)" else "" in
      eprint lc "Definition of symbol '%a'%s." pp_ident id opaque_str;
      let cst = mk_name md id in
      Termination.add_constant cst Definable ty;
      let rule = { name= Delta(cst) ;
                   ctx = [] ;
                   pat = Pattern(l, cst, []);
                   rhs = te ;
                 }
      in Termination.add_rules [Rule.to_rule_infos rule]
    end
  | Rules(rs) ->
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
      Termination.add_rules (List.map to_rule_infos rs)
    end
  | Eval(_,_,_)
  | Infer(_,_,_)
  | Check(_, _, _, _)
  | DTree(_, _, _)
  | Print(_, _)
  | Name(_, _) -> ()
  | Require(lc,md) ->
      Termination.import lc md

let run_on_file file =
  let input = open_in file in
  Debug.(debug d_module "Processing file '%s'..." file);
  let md = mk_mident file in
  Termination.initialize ();
  Parser.handle_channel md (mk_entry md) input;
  Termination.termination_check ();
  close_in input

let _ =
  let run_on_stdin = ref None  in
  let options = Arg.align
    [ ( "-d"
      , Arg.String Debug.set_debug_mode
      , "flags enables debugging for all given flags" )
    ; ( "-v"
      , Arg.Unit (fun () -> Debug.set_debug_mode "montru")
      , " Verbose mode (equivalent to -d 'w')" )
    ; ( "-q"
      , Arg.Unit (fun () -> Debug.set_debug_mode "q")
      , " Quiet mode (equivalent to -d 'q'" )
    ; ( "-nc"
      , Arg.Clear Errors.color
      , " Disable colors in the output" )
    ; ( "-stdin"
      , Arg.String (fun n -> run_on_stdin := Some(n))
      , "MOD Parses standard input using module name MOD" )
    ; ( "-version"
      , Arg.Unit (fun () -> Format.printf "Dedukti %s@." Version.version)
      , " Print the version number" )]
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
  | Parse_error(loc,msg) -> Format.eprintf "Parse error at (%a): %s@." pp_loc loc msg; exit 1
  | Sys_error err        -> Format.eprintf "ERROR %s.@." err; exit 1
  | Exit                 -> exit 3
