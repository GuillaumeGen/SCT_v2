open Term
open Basic
open Parser
open Entry

exception Unpack_Failed

let unpack_err : ('a,'b) error -> 'a = function
  | OK a  -> a
  | Err _ -> raise Unpack_Failed

let compose f g = fun x -> f (g x)
                   
let eprint lc fmt =
  Debug.(debug d_notice ("%a " ^^ fmt) pp_loc lc)

let mk_entry md e =
  match e with
  | Decl(lc,id,st,ty) ->
    begin
      eprint lc "Declaration of constant '%a'." pp_ident id;
      begin
        match Env.declare lc id st ty with
        | OK () -> ()
        | Err e -> Errors.fail_env_error e
      end;
      let cst = mk_name md id in
      Termination.add_constant cst st ty
    end
  | Def(lc,id,opaque,ty,te) ->
    begin
      let opaque_str = if opaque then " (opaque)" else "" in
      eprint lc "Definition of symbol '%a'%s." pp_ident id opaque_str;
      begin
        let define = if opaque then Env.define_op else Env.define in
        match define lc id te ty with
        | OK () -> ()
        | Err e -> Errors.fail_env_error e
      end;
      let cst = mk_name md id in
      begin
        match ty with
        | Some tt -> Termination.add_constant cst Definable tt
        | None    ->
           Termination.add_constant cst Definable (unpack_err (Env.infer te))
      end;
      let rul : Rule.untyped_rule = { name= Delta(cst) ;
                   ctx = [] ;
                   pat = Pattern(lc, cst, []);
                   rhs = te ;
                 }
      in Termination.add_rules [unpack_err (Rule.to_rule_infos rul)]
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
      begin
        match Env.add_rules rs with
        | OK rs -> List.iter (eprint (get_loc_pat r.pat) "%a" pp_typed_rule) rs
        | Err e -> Errors.fail_env_error e
      end;
      Termination.add_rules (List.map (compose unpack_err to_rule_infos) rs)
    end
  | Eval(_,_,_)
  | Infer(_,_,_)
  | Check(_, _, _, _)
  | DTree(_, _, _)
  | Print(_, _)
  | Name(_, _) -> ()
  | Require(lc,md) ->
      begin
        match Env.import lc md with
        | OK () -> ()
        | Err e -> Errors.fail_signature_error e
      end;
      Termination.import lc md

let run_on_file file =
  let input = open_in file in
  Debug.(debug d_module "Processing file '%s'..." file);
  let md = Env.init file in
  Termination.initialize ();
  Rule.allow_non_linear := true;
  Parser.handle_channel md (mk_entry md) input;
  if Termination.termination_check ()
  then Format.printf "YES"
  else Format.printf "MAYBE";
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
