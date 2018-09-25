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
type local_result = SelfLooping of (index list)

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


(** A call [{callee; caller; matrix; is_rec}] represents a call to the function symbol with key [callee] by the function symbole with the key [caller].
    The [matrix] gives the relation between the parameters of the caller and the callee.
    The coefficient [matrix.(a).(b)] give the relation between the [a]-th parameter of the caller and the [b]-th argument of the callee.
    [rules] is the list of indexes of rules which lead to this call-matrix in the graph. *)
type call =
  { callee      : index      ; (** Key of the function symbol being called. *)
    caller      : index      ; (** Key of the calling function symbol. *)
    matrix      : matrix     ; (** Size change matrix of the call. *)
  }

(** Internal state of the SCT, including the representation of symbols and the call graph. *)
type call_graph =
  {
    next_index      : index ref             ; (** The index of the next function symbol to be added *)
    symbols         : symbol IMap.t ref     ; (** A map containing every symbols studied *)
    calls           : call list ref         ; (** The list of every call *)
  }

(** Create a new graph *)
let new_graph : unit -> call_graph =
  fun () ->
    let syms = IMap.empty in
    { next_index = ref 0; symbols = ref syms ; calls = ref [] }

let find_name : call_graph -> index -> string =
  fun gr i ->
    (IMap.find i !(gr.symbols)).name

(** The pretty printer for the type [call]. *)
let pp_call : call_graph -> call printer=
  fun gr fmt c ->
    let res=ref "" in
    for i=0 to c.matrix.h -1 do
      res:=!res^"x"^(string_of_int i)^" "
    done;
    Format.fprintf fmt "%s(%s%!) <- %s%!("
      (find_name gr c.caller)
      !res (find_name gr c.callee);
    let jj=Array.length c.matrix.tab in
    if jj>0 then
      let ii=Array.length c.matrix.tab.(0) in
      for i = 0 to ii - 1 do
        if i > 0 then Format.fprintf fmt ",";
        let some = ref false in
        for j = 0 to jj - 1 do
          let c = c.matrix.tab.(j).(i) in
          if c <> Infi then
            begin
              let sep = if !some then " " else "" in
              Format.fprintf fmt "%s%s" sep (cmp_to_string c);
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

(** Add a new call to the call graph. *)
let add_call : call_graph -> call -> unit =
  fun gr cc ->
    Debug.debug D_graph "New call: %a" (pp_call gr) cc;
    gr.calls := cc :: !(gr.calls)

(** Add a new symb to the call graph *)
let add_symb : call_graph -> symbol -> unit =
  fun gr sy ->
    gr.symbols := IMap.add !(gr.next_index) sy !(gr.symbols);
    incr gr.next_index

let graph : call_graph ref = ref (new_graph ())

let index_and_arity_of : call_graph -> string -> index*int =
  fun gr s ->
    let symb = !(gr.symbols) in
    let k,sym = IMap.find_first (fun k -> (IMap.find k symb).name = s) symb in
    k, sym.arity
    
