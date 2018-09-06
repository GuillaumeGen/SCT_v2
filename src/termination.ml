open Basic
open Term
open Rule
open Sizematrix
open Callgraph
open Sizechange
open Positivity

let imported_modules=ref []
       
type global_result=Terminating | G_SelfLooping
                  | G_UsingBrackets | G_NonPositive 
                  | G_NotHandledRewritingTypeLevel
                  | G_Coc


let pp_global_result : global_result printer =
  fun fmt gr ->
    let st =
      match gr with
          | Terminating -> "Terminating"
          | G_SelfLooping -> "Self Looping"
          | G_UsingBrackets -> "Using Brackets"
          | G_NonPositive -> "Non positive"
          | G_NotHandledRewritingTypeLevel -> "Not Handled Rewriting"
          | G_Coc -> "Coc option is uncompatible with sz"
    in Format.fprintf fmt "%s" st

(** This table contains the name of functions corresponding to each potential global_result *)
let table_result : (global_result, name list) Hashtbl.t =
  Hashtbl.create 6
(* Here 6 is not arbitrary since there is 6 global result *)

(** This list contains for each looping symbol one list of rules causing this loop *)
let list_SelfLooping : (name * index list) list ref
  = ref []

(** This function clean all the global variables, in order to study another file *)
let initialize : unit -> unit =
  fun ()->
  let syms = NMap.empty in
  let ruls = IMap.empty in
  graph:={ next_index = ref 0 ; next_rule_index = ref 0; symbols = ref syms ;
           all_rules = ref ruls ; calls = ref [] };
  Hashtbl.clear must_be_str_after;
  Hashtbl.clear after;
  Hashtbl.clear table_result;
  list_SelfLooping := [];
  imported_modules := []
  
                        
(** Creation of a new symbol.  *)
let create_symbol : name -> int -> symb_status -> term -> unit =
  fun identifier arity status typ->
    let g= !graph in
    if NMap.mem identifier !(g.symbols)
    then ()
    else
      let ind = !(g.next_index) in
      Format.(printf "Adding the %a symbol %a of arity %i at index %a"
        pp_status status pp_name identifier arity pp_index ind);
      let sym = {ind ; arity ; typ; status; result=[]} in
      g.symbols := NMap.add identifier sym !(g.symbols);
      incr g.next_index

(** Creation of a new rule.  *)
let create_rule : rule_infos -> unit =
  fun r ->
    let g= !graph in
    Format.(printf "Adding the rule %a"
        pp_rule_infos r); 
    let index = !(g.next_rule_index) in
    g.all_rules := IMap.add index r !(g.all_rules);
    incr g.next_rule_index




let corresp_loc_glob = function
  | UsingBrackets -> G_UsingBrackets
  | NonPositive -> G_NonPositive
  | NotHandledRewritingTypeLevel -> G_NotHandledRewritingTypeLevel
  | CocOption -> G_Coc
  | _ -> assert false

let analyse_result : unit -> unit =
  fun () ->
    let tbl= !(!graph.symbols) in
    let rec fill_res_HT b id =
      let modify_ht x tl=
        updateHT table_result (corresp_loc_glob x) id;
        fill_res_HT false id tl
      in
      function
      | []                 -> if b then updateHT table_result Terminating id
      | SelfLooping(l)::tl ->
        begin
          list_SelfLooping := (id,l):: !list_SelfLooping;
          fill_res_HT false id tl
        end
      | x ::tl -> modify_ht x tl
    in
    NMap.iter
      (fun k s -> fill_res_HT (s.status != Set_constructor)
          k s.result
      ) tbl

(** Take all the rules headed by a symbol and add them to the call graph *)
let rec add_rules : rule_infos list -> unit =
  fun l ->
    List.iter load_rules l;
    List.iter create_rule l;
     Format.(printf "Ajout des règles : @. - %a"
        (pp_list "\n - " pp_rule_infos) l);
    let ll=List.flatten (List.map (rule_to_call 0) l) in
    if ll=[] then Format.(printf "Liste de call vide générée");
    List.iter add_call ll
      
and add_constant : name -> Signature.staticity -> term -> unit
  = fun fct stat typ ->
    try
      load_terms typ;
      let rm = right_most typ in
      let status =
        (
          match rm,stat with
          | Type _, Signature.Definable -> Def_type
          | Type _, Signature.Static    -> Set_constructor
          | _     , _                   -> Def_function
        )
      in
      create_symbol fct (infer_arity_from_type typ) status typ;
      match rm with
      | App(Lam(_),_,_) -> update_result fct NotHandledRewritingTypeLevel
      | _ -> ()
    with Coc ->
      begin
        create_symbol fct 0 Def_function typ;
        update_result fct CocOption
      end
      
and import : loc -> mident -> unit =
  fun lc m ->
  if m = Env.get_name () || List.mem m !imported_modules
  then ()
  else
    begin
      imported_modules:= m:: !imported_modules;
      let (deps,ctx,ext) = Signature.read_dko lc (string_of_mident m) in
      let symb (id,stat,ty,_) =
        let cst = mk_name m id in
        add_constant cst stat ty;
      in
      let rul (id,stat,ty,rul) =
        add_rules rul
      in
      List.iter symb ctx;
      List.iter rul ctx
    end
    
and load_terms : Term.term -> unit =
  function
  | Term.Kind 
  | Term.Type _
  | Term.DB (_, _, _) -> ()
  | Term.Const (lc, n) -> import lc (md n)
  | Term.App (t, u, l) -> List.iter load_terms (t::u::l)
  | Term.Lam (_, _, Some ty, te) -> load_terms ty; load_terms te
  | Term.Lam (_, _, None, te) -> load_terms te
  | Term.Pi (_, _, t1, t2) -> load_terms t1; load_terms t2

and load_patterns = function
  | Rule.Var (_,_,_,l) -> List.iter load_patterns l
  | Rule.Pattern (lc, n, l) -> import lc (md n); List.iter load_patterns l
  | Rule.Lambda (_, _, p) -> load_patterns p
  | Rule.Brackets t -> load_terms t

and load_rules r =
  let lc = r.l in
  import lc (md r.cst);
  load_terms r.rhs;
  List.iter load_patterns r.args

(** Do the SCT-checking *)	
let termination_check () =
  NMap.iter
    (fun fct sym ->
       let tt = sym.typ in
       constructors_infos Global fct tt (right_most tt)
    )
    (
      NMap.filter
        (fun _ symb ->
           List.mem symb.status [Elt_constructor; Set_constructor]
        )
        !(!graph.symbols)
    );
  let tarj = tarjan after in
   Format.(printf "After :@.%a" (pp_HT pp_name (pp_list "," pp_name)) after);
   Format.(printf "%a" (pp_list ";" (pp_list "," pp_name)) tarj);
  sct_only ();
  (* Test positivity of the signature *)
  str_positive tarj must_be_str_after;
  analyse_result ();
  let tbl= !(!graph.symbols) in
  NMap.for_all
    (fun _ s-> s.result = []) tbl

let pp_list_of_self_looping_rules : (name *index list) printer =
  fun fmt (x,y) ->
    Format.fprintf fmt "%a\n%a" pp_name x
      (pp_list "\n"
         (fun fmt ind ->
            let r=IMap.find ind !(!graph.all_rules) in
            Format.fprintf fmt "{%a} %a %a --> %a"
              pp_rule_name r.name
              pp_name r.cst
              (pp_list " " pp_pattern) r.args
              pp_term r.rhs
         )
      ) y

