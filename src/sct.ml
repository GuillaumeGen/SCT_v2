open Basic
open Dk

let perform_checks : Callgraph.call_graph -> bool =
  fun gr ->
  Sizechange.check_sct gr
  && Arity_checker.check_lh_arity gr.signature
  && Pfp_checker.check_pfp gr
  && Rhs_typability.check_rhs_underf_typab gr

let run_on_file file=
  let input = open_in file in
  let md = Filename.remove_extension (Filename.basename file) in
  let ext = Filename.extension file in
  let gr =
    if ext = ".dk"
    then
      let s =
        to_dk_signature file (Parser.Parse_channel.parse (mk_mident md) input)
      in Dk.dk_sig_to_callgraph s
    else if ext = ".xml"
    then
      begin
        let md2 = mk_mident file in
        let dk_string = Tpdb_to_dk.load md2 file in
        if !(Tpdb_to_dk.export_dk_file)
        then
          (let output = Format.formatter_of_out_channel (open_out (md^".dk")) in
           Format.fprintf output "%s@." dk_string);
        let s =
          to_dk_signature file (Parser.Parse_string.parse (mk_mident md) dk_string)
        in Dk.dk_sig_to_callgraph s
      end
    else failwith "Not handled file extension"
  in
  close_in input;
  perform_checks gr
