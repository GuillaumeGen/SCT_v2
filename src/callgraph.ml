open Basic
open Symbols
open Sizematrix
       
type Debug.flag += D_graph | D_call
let _ = Debug.register_flag D_graph "Call graph";
  Debug.register_flag D_call "Call generation"

(** Map with index as keys. *)
module IMap =
  struct
    include Map.Make(
      struct
        type t = index
        let compare = compare
      end)
  end

module EdgeLabel = struct
  type t = (string list * Cmp_matrix.t) list

  let pp : t printer =
    fun fmt l ->
      Format.fprintf fmt "[%a]"
        (pp_list ",@." (fun fmt (a,b) -> Cmp_matrix.pp fmt b)) l

  let add_neutral : t = []

  let plus : t -> t -> t =
    let compare_cmp_matrix (m1 : Cmp_matrix.t) (m2 : Cmp_matrix.t) =
      assert (m1.h = m2.h);
      assert (m1.w = m2.w);
      let res = ref 0 in
      for i = 0 to m1.h -1 do 
        for j = 0 to m1.w -1 do
          if !res = 0
          then 
            res := Cmp.compare_Cmp m1.tab.(i).(j) m2.tab.(i).(j)
        done;
      done; !res
    in
    fun l1 l2 ->
      List.sort_uniq
        (fun (_,a) (_,b) -> compare_cmp_matrix a b) (List.append l1 l2)

  let mult : t -> t -> t =
    fun l1 l2 ->
      List.flatten (
        List.map (
          fun (r1,x) ->
            List.map (fun (r2,y) -> (r1@r2,Cmp_matrix.prod x y)) l2
        ) l1
      )
end

module CallGraphAdjMat = Matrix(EdgeLabel)

(** Internal state of the SCT, including the representation of symbols and the call graph. *)
type call_graph =
  {
    next_index      : index ref             ; (** The index of the next function symbol to be added *)
    symbols         : symbol IMap.t ref     ; (** A map containing every symbols studied *)
    calls           : CallGraphAdjMat.t  ref; (** The adjacence matrix of the call graph *)
  }

(** Create a new graph *)
let new_graph : unit -> call_graph =
  fun () ->
    let symbs = IMap.empty in
    {
      next_index = ref 0;
      symbols = ref symbs;
      calls = ref (CallGraphAdjMat.new_mat 0)
    }

let copy_graph : call_graph -> call_graph =
  fun g ->
  let next_index = ref !(g.next_index) in
  let symbols = ref IMap.empty in
  IMap.iter (fun a b-> symbols := IMap.add a b !symbols) !(g.symbols);
  let calls = ref (CallGraphAdjMat.copy !(g.calls)) in
  {next_index; symbols; calls}
  
      
let find_name : call_graph -> index -> string =
  fun gr i ->
    (IMap.find i !(gr.symbols)).name

type call = {caller    : index;
             callee    : index;
             matrix    : Cmp_matrix.t;
             rule_name : string}

(** The pretty printer for the type [call]. *)
let pp_call : call_graph -> call printer=
  fun gr fmt cc ->
    let res=ref "" in
    let h = cc.matrix.h -1 in
    for i=0 to h do
      res:=!res^"x"^(string_of_int i);
      if i < h then res := !res^" "
    done;
    Format.fprintf fmt "%s(%s%!) <- %s%!("
      (find_name gr cc.caller)
      !res (find_name gr cc.callee);
    let jj=cc.matrix.h in
    if jj>0 then
      let ii=cc.matrix.w in
      for i = 0 to ii - 1 do
        if i > 0 then Format.fprintf fmt ",";
        let some = ref false in
        for j = 0 to jj - 1 do
          let c = cc.matrix.tab.(j).(i) in
          if c <> Cmp.infi then
            begin
              let sep = if !some then " " else "" in
              Format.fprintf fmt "%s%s" sep (Cmp.cmp_to_string c);
              some := true
            end
        done
      done;
      Format.fprintf fmt ")"

(** Those functions modify the mutable fields in the symbol records *)
let update_result : call_graph -> index -> local_result -> unit =
  fun gr i res ->
    let tbl = !(gr.symbols) in
    let sy = (IMap.find i tbl) in
    sy.result <- res::sy.result

(** Compute the transitive closure of a call_graph *)
let rec trans_clos : call_graph -> unit =
  fun gr ->
    let m = !(gr.calls) in
    let mm = CallGraphAdjMat.sum m (CallGraphAdjMat.prod m m) in
    if m = mm
    then ()
    else (
      gr.calls := mm;
      trans_clos gr)

(** Add a new call to the call graph.
    We maintain the transitive closure computed at each step. *)
let add_call : call_graph -> call -> unit =
  fun gr cc ->
    Debug.debug D_graph "New call: %a" (pp_call gr) cc;
    Debug.debug D_graph "The matrix is %a" Cmp_matrix.pp cc.matrix;
    !(gr.calls).tab.(cc.caller).(cc.callee) <-
      ([cc.rule_name],cc.matrix) :: !(gr.calls).tab.(cc.caller).(cc.callee);
    trans_clos gr

(** Add a new symb to the call graph *)
let add_symb : call_graph -> symbol -> unit =
  fun gr sy ->
    Debug.debug D_graph "We add the symbol (%i,%s)" !(gr.next_index)  sy.name;
    gr.symbols := IMap.add !(gr.next_index) sy !(gr.symbols);
    incr gr.next_index;
    gr.calls := CallGraphAdjMat.(add_line (add_column !(gr.calls)))

let graph : call_graph ref = ref (new_graph ())

let initialize : unit -> unit =
  fun () -> graph := new_graph (); cstr := []
        
exception Success_index  of index

(** [find_rule_key r] will return the key [k] which is mapped to the rule [r] *)
let find_symbol_key : call_graph -> string ->  index
  = fun gr s ->
    try
      IMap.iter
        (
	  fun k x -> if x.name = s then raise (Success_index k)
        ) !(gr.symbols);
      raise Not_found
    with Success_index k -> k

let index_and_arity_of : call_graph -> string -> index*int =
  fun gr s ->
    let symb = !(gr.symbols) in
    let k = find_symbol_key gr s in
    k, (arity_of (IMap.find k symb).typ)
         
let definable : call_graph -> string -> bool =
  fun gr s ->
    let k = find_symbol_key gr s in
    Array.exists (fun l -> not (l = [])) !(gr.calls).tab.(k)
