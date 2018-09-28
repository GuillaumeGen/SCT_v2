open Basic
open Sizematrix

type Debug.flag += D_graph | D_call
let _ = Debug.register_flag D_graph "Call graph";
  Debug.register_flag D_call "Call generation"

(** Index of a rule. *)
type index = int

(** Conversion to int. *)
let int_of_index : index -> int =
  fun i -> i

(** The pretty printer for the type [index] *)
let pp_index fmt x =
  Format.pp_print_int fmt (int_of_index x)

(** The local result express the result of the termination checker for this symbol *)
type local_result = SelfLooping of string list

(** The pretty printer for the type [local_result] *)
let pp_local_result : local_result printer =
  fun fmt lr ->
    let st =
      match lr with
      | SelfLooping _ -> "Self Looping"
    in
    Format.fprintf fmt "%s" st
  
(** Representation of a function symbol. *)
type symbol =
  {
    name           : string            ; (** The identifier of the symbol *)
    arity          : int               ; (** Arity of the symbol (number of args). *)
    mutable result : local_result list ; (** The information about non termination for this symbol, initially empty *)
  }

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
            res := Cmp.(match (m1.tab.(i).(j),m2.tab.(i).(j)) with
              | Infi, Infi -> 0
              | Infi, _    -> 1
              | _   , Infi -> -1
              | Zero, Zero -> 0
              | Zero, Min1 -> 1
              | Min1, Zero -> -1
              | Min1, Min1 -> 0)
        done
      done; !res in
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
    let syms = IMap.empty in
    {
      next_index = ref 0;
      symbols = ref syms;
      calls = ref (CallGraphAdjMat.new_mat 0)
    }

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
    for i=0 to cc.matrix.h -1 do
      res:=!res^"x"^(string_of_int i)^" "
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
          if c <> Cmp.Infi then
            begin
              let sep = if !some then " " else "" in
              Format.fprintf fmt "%s%s" sep (Cmp.cmp_to_string c);
              some := true
            end
        done
      done;
      Format.fprintf fmt ")%!"

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
    !(gr.calls).tab.(cc.caller).(cc.callee) <-
      ([cc.rule_name],cc.matrix) :: !(gr.calls).tab.(cc.caller).(cc.callee);
    trans_clos gr

(** Add a new symb to the call graph *)
let add_symb : call_graph -> symbol -> unit =
  fun gr sy ->
    gr.symbols := IMap.add !(gr.next_index) sy !(gr.symbols);
    incr gr.next_index;
    let tab =
      Array.init !(gr.next_index)
        (fun i ->
           Array.init !(gr.next_index)
             (fun j ->
                try !(gr.calls).tab.(i).(j)
                with _ -> []
             )
        ) in
    gr.calls := {h = !(gr.calls).h +1; w = !(gr.calls).w +1; tab}

let graph : call_graph ref = ref (new_graph ())

let initialize : unit -> unit =
  fun () -> graph := new_graph ()
        
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
    let sym = IMap.find k symb in
    k, sym.arity
         
