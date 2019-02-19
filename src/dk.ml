open Basic
open Term
open Entry
open Sign
open Callgraph
open Call_extractor

let str_of_name = string_of pp_name

let term_iter : (int -> ident -> unit) -> (name -> unit) -> unit -> term -> unit =
  fun f_var f_cst f_typ ->
  let rec aux =
    function
    | Kind               -> ()
    | Type _             -> f_typ
    | DB(_,x,i)          -> f_var i x
    | Const(_,f)         -> f_cst f
    | App(t,u,tl)        -> List.iter aux (t::u::tl)
    | Lam(_,_,None,t)    -> aux t
    | Lam(_,_,Some a, t) -> aux a; aux t
    | Pi(_,_,a,b)        -> aux a; aux b
  in aux
                
let pre_rule_of_rinfos : Rule.rule_infos -> Rules.pre_rule =
  fun r ->
  let name =
    match r.name with
    | Rule.Beta       -> "β"
    | Rule.Delta(s)   -> Format.asprintf "Def of %s" (str_of_name s)
    | Rule.Gamma(_,s) -> Format.asprintf "Rule %s" (str_of_name s)
  in
  let args = Array.of_list (List.map Rule.pattern_to_term r.args) in
  let ctx = Array.init r.esize (fun _ -> dmark) in
  
  {name; args; rhs = r.rhs; head = r.cst; ctx}
                
let add_symb_infos : call_graph -> Signature.symbol_infos -> call_graph =
  fun gr sy ->
  let sym = new_symb sy.ident sy.ty in
  let res = ref (add_symb gr sym) in
  List.iter (fun r -> res := add_rule !res (pre_rule_of_rinfos r)) sy.rules;
  !res

let dk_sig_to_callgraph : Signature.t -> call_graph =
  fun s ->
  let l = Signature.access_signature s in
  let rec enrich gr =
    function
    | []    -> gr
    | a::tl -> enrich (add_symb_infos gr a) tl
  in enrich (new_graph ()) l

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
       let rule = { name= Delta(cst) ; ctx = [] ; pat = Pattern(lc, cst, []); rhs = te } in
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
