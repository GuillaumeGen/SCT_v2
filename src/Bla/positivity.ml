open Sizematrix
open Callgraph

(** [frozen gr rn typ] return [true] if [typ] is a product of potentially applied type constants *)
let rec frozen : call_graph -> string -> typ -> bool =
  fun gr rn -> function
    | Type 
    | Unhandled -> false
    | Cst f ->
      if definable gr f
      then
        let gr = !graph in
        update_result gr (find_symbol_key gr f) (DefinableType rn);
        false
      else true
    | Prod (l, t) -> List.for_all (frozen gr rn) (t::l)

type constr_graph =
  {
    constructors : string array      ; (** An array containing every symbols studied *)
    is_after     : Bool_matrix.t ref ; (** The adjacence matrix of the call graph *)
  }

(** [extract_constraints_of_typ t_arg] return the list of type constructors which occur in positive position in [t_arg] and the list of type constructors which occur in negative position in [t_arg]. *)
let extract_constraints_of_typ : typ -> string list * string list =
  let rec extract_positive : typ -> string list =
    function
    | Cst f -> [f]
    | Prod (l, Cst f) -> f::(List.flatten (List.map extract_negative l))
    | _ -> assert false (** Since those types are not frozen, they should not be argument of [extract_constraints_of_typ] *)
  and extract_negative : typ -> string list =
    function
    | Cst f -> []
    | Prod (l, Cst f) -> List.flatten (List.map extract_positive l)
    | _ -> assert false in
  fun t_arg -> (extract_positive t_arg,extract_negative t_arg)

let create_cstr_graph : (string * string * typ * string) list -> constr_graph =
  fun cstr_l ->
  let get_array_useful_type_cst : (string * string * typ * string) list -> string array =
    let rec get_cst_of_typ =
      function
      | Cst f -> [f]
      | Prod (l,t) -> List.flatten (List.map get_cst_of_typ (t::l))
      | _ -> assert false in
    fun cst ->
    Array.of_list
      (List.sort_uniq compare
         (List.flatten
            (List.map (fun (c,f,t,rn) -> f::(get_cst_of_typ t)) cst)
         )
      ) in
  let constructors = get_array_useful_type_cst cstr_l in
  {constructors; is_after = ref (Bool_matrix.diago (Array.length constructors))}

(** [check_strict_decrease gr (a,b)] returns [true] if the [b]th symbol is strictly smaller than the [a]th meaning that the [b]th is smaller than the [a]th and the [a]th is not smaller than the [b]th *)
let check_strict_decrease : constr_graph -> int * int -> bool =
  fun gr (a,b) ->
  let mat = !(gr.is_after).tab in
  (not mat.(a).(b)) && mat.(b).(a)
  
let rec transitive_closure : constr_graph -> unit =
  fun gr ->
  let m = !(gr.is_after) in
  let mm = Bool_matrix.sum m (Bool_matrix.prod m m) in
  if not (m = mm) then
    (gr.is_after := mm;
     transitive_closure gr)

let check_positivity : call_graph -> (string * int * string) list -> bool =
  let find : 'a -> 'a array -> int =
    let i = ref (-1) in
    fun x l ->
    for j = 0 to Array.length l -1 do
      if l.(j)=x then i:=j
    done;
    !i in
  fun gr cst ->
  let translate : (string * int * string) -> (string * string * typ * string) =
    fun (c,i,rn) ->
    match (IMap.find (find_symbol_key gr c) !(gr.symbols)).typ with
    | Prod(l,Cst f) -> (c,f,List.nth l i,rn)
    | _ -> assert false in
  let cst_l = List.map translate cst in
  let b_l = List.map (fun (c,f,t,rn) -> frozen gr rn t) cst_l in
  if List.for_all (fun x -> x) b_l
  then
    let c_graph = create_cstr_graph cst_l in
    let symbs = c_graph.constructors in
    let tab = !(c_graph.is_after).tab in
    let cstr =
      List.map
        (fun (c,f,t,rn) -> (c,f,rn,extract_constraints_of_typ t))
        cst_l in
    let cstr =
      List.flatten
        (List.map
           (fun (c,f,rn,(l_p,l_n)) ->
             let ff = find f symbs in
             List.iter (fun p -> tab.(find p symbs).(ff) <- true) l_p;
             List.map
               (fun n ->
                 let nn = find n symbs in
                 tab.(nn).(ff) <- true;
                 (c,rn,ff,nn)
               ) l_n
           )
           cstr
        ) in
    transitive_closure c_graph;
    let a = ref true in
    List.iter
      (fun  (c,rn,i,j) ->
        if not (check_strict_decrease c_graph (i,j))
        then
          (a:=false;
           update_result gr (find_symbol_key gr c) (NotPositive rn))
      )
      cstr;
    !a
  else false
