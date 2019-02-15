open Basic
open Entry

let to_dk_signature : string -> entry list -> Signature.t =
  fun path entries ->
  let sg = Signature.make path in
  let md = Signature.get_name sg in
  let mk_entry = function
    | Decl(lc,id,st,ty) ->
       Signature.add_external_declaration sg lc (Basic.mk_name md id) st ty
    | Def(lc,id,op,Some ty,te) ->
       let open Rule in
       Signature.add_external_declaration sg lc (Basic.mk_name md id) Signature.Definable ty;
       let cst = Basic.mk_name md id in
       let rule = { name= Delta(cst) ; ctx = [] ; pat = Pattern(lc, cst, []); rhs = te ; } in
       Signature.add_rules sg [Rule.to_rule_infos rule]
    | Def(lc,id,op, None,te) ->
       Errors.fail_exit (-1) Basic.dloc "All the types should be given"
    | Rules(lc,rs) ->
       Signature.add_rules sg (List.map Rule.to_rule_infos rs)
    | Require(lc,md) -> Signature.import sg lc md
    | _ -> ()
  in
  List.iter mk_entry entries;
  sg

let run_on_file file=
  let gr = Callgraph.new_graph () in
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
      to_dk_signature file (Parser.Parse_channel.parse (mk_mident md) input)
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
  if Positivity.check_positivity !Callgraph.graph !Sizematrix.cstr &&
       Sizechange.check_sct !Callgraph.graph
  then Format.eprintf "%s@." (green "YES")
  else
    begin
      Format.eprintf "%s@." (orange "MAYBE");
      let lc_result : Callgraph.symbol -> unit =
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
