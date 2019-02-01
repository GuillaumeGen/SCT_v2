(** Tools used for the matrices labeling edges in the call-graph studied by sizechange.ml *)

open Basic
open Symbols

type Debug.flag += D_matrix
let _ = Debug.register_flag D_matrix "Call matrix"

module type SemiRing = sig
  type t
  val pp          : t printer
  val add_neutral : t
  val plus        : t -> t -> t
  val mult        : t -> t -> t
end

module Matrix = functor (SR : SemiRing) -> struct
  type t = {h : int; w : int; tab : SR.t array array}

  (** The pretty printer for the type [matrix] *)
  let pp : t printer = fun fmt m ->
    Format.fprintf fmt "[[%a]]"
      (pp_arr "]\n [" (pp_arr "," SR.pp)) m.tab

  let copy : t -> t =
    fun x ->
    let h = x.h in
    let w = x.w in
    let tab = Array.init h (fun a -> Array.copy x.tab.(a)) in
    {h; w; tab}
      
  let sum : t -> t -> t =
    fun m1 m2 ->
      assert (m1.h = m2.h);
      assert (m1.w = m2.w);
      let tab = Array.init m1.h
        (fun y->
	   Array.init m1.w
             (fun x ->
                SR.plus m1.tab.(y).(x) m2.tab.(y).(x)
             )
        )
      in {h=m1.h; w=m1.w; tab}
    
  let prod : t -> t -> t =
    fun m1 m2 ->
      assert (m1.w = m2.h);
      (* The matrix must be compatible to perform product *)
      let tab = Array.init (m1.h)
        (fun y ->
	   Array.init (m2.w)
             (fun x ->
                let r = ref SR.add_neutral in
                for k = 0 to m1.w -1 do
	          r := SR.plus !r (SR.mult m1.tab.(y).(k) m2.tab.(k).(x))
                done; !r
             )
        ) in
      let mat = {h = m1.h; w = m2.w; tab} in
      mat

  (** Check if a matrix is square *)
  let is_idempotent : t -> bool =
    fun m ->
      assert (m.h = m.w);
      (* only square matrix can be idempotent *)
      m = (prod m m)
        
  (** Create a new square matrix of size [n] *)
  let new_mat : int -> t =
    fun n ->
      let tab= Array.init n (fun i -> Array.init n (fun j -> SR.add_neutral))
      in {h=n; w=n; tab}

  let add_line : t -> t =
    fun m ->
      {h = m.h+1; w = m.w; 
        tab = Array.init (m.h +1)
                (fun i ->
                   Array.init m.w
                     (fun j ->
                        if i<m.h then m.tab.(i).(j) else SR.add_neutral
                     )
              )}
      
  let add_column : t -> t =
    fun m ->
      {h = m.h; w = m.w+1; 
        tab = Array.init m.h
                (fun i ->
                   Array.init (m.w +1)
                     (fun j ->
                        if j<m.w then m.tab.(i).(j) else SR.add_neutral
                     )
                )}
end

module Cmp = struct

  type condition = Sm of index * index | Eq of index * index

  let pp_cond : condition printer =
    fun fmt ->
    function
    | Sm(i,j) -> Format.fprintf fmt "Sm(%i,%i)" i j
    | Eq(i,j) -> Format.fprintf fmt "Eq(%i,%i)" i j
                                                         
  type dnf = condition list list

  let pp_dnf : dnf printer =
    pp_list ";" (pp_list "," pp_cond)
               
  let ou : dnf -> dnf -> dnf =
    fun l1 l2 -> l1 @ l2

  let et : dnf -> dnf -> dnf =                        
    fun l1 l2 -> List.flatten (List.map (fun x -> List.map (fun y -> x@y) l1) l2)
                              
  type t = dnf * dnf
                      
  let rec rm_duplicate : 'a list -> 'a list =
    function
    | [] -> []
    | a::l -> if List.mem a l then rm_duplicate l else a::(rm_duplicate l)
                                                            
  let useless_decr : dnf -> dnf =
    let rec bis : dnf -> dnf -> dnf =
      fun acc ->
      function
      | []   -> acc
      | h::l ->
         if List.exists (fun x -> List.for_all (fun y -> List.mem y h) x) (acc@l)
         then bis acc l
         else bis ((rm_duplicate h)::acc) l
    in bis []

  let comp_cond : condition -> condition -> int =
    fun c1 c2 ->
    match c1,c2 with
    | Sm(a,b), Sm(c,d)
    | Eq(a,b), Eq(c,d)->
       let res = compare a c in
       if res = 0
       then compare b d
       else res
    | Sm(_,_),_ -> 1
    | Eq(_,_),_ -> -1
                                
  let comp_dnf : dnf -> dnf -> int =
    let rec comp_cond_list : condition list -> condition list -> int =
      fun l1 l2 ->
      match l1, l2 with
      | [],[] -> 0
      | [],_  -> 1
      | _, [] -> -1
      | a::b,c::d ->
         let res = comp_cond a c in
         if res = 0
         then comp_cond_list b d
         else res
    in
    let rec comp_sorted_dnf : dnf -> dnf -> int =
      fun l1 l2 ->
      match l1,l2 with
      | [],[] -> 0
      | [],_  -> 1
      | _, [] -> -1
      | a::b,c::d ->
         let res = comp_cond_list a c in
         if res = 0
         then comp_sorted_dnf b d
         else res
    in
    fun l1 l2 ->
    let ll1 = List.map (List.sort_uniq comp_cond) l1 in
    let ll2 = List.map (List.sort_uniq comp_cond) l2 in
    comp_sorted_dnf ll1 ll2
                 
                                
  let clean : t -> t=
    let useless_eq : t -> t =
      let rec bis : dnf -> t -> t =
        fun acc ->
      function
      | a,[]   -> a,acc
      | a,h::l ->
         if List.exists (fun x -> List.for_all (fun y -> List.mem y h) x) (a@acc@l)
         then bis acc (a,l)
         else bis ((rm_duplicate h)::acc) (a,l)
      in bis []
    in fun (a,b) -> useless_eq ((useless_decr a),b)
                               
  let compare_Cmp : t -> t -> int =
    fun (sm1,eq1) (sm2,eq2) ->
    let res = comp_dnf sm1 sm2 in
    if res = 0
    then comp_dnf eq1 eq2
    else res
                               
  (** String representation. *)
  let cmp_to_string : t -> string =
    function
    | []  ,[]   -> "∞ "
    | []  ,[[]] -> "= "
    | []  ,_    -> "?="
    | [[]],[]   -> "< "
    | l1  ,_ ->
       Format.asprintf "[%a]"
         (pp_list ";"
            (fun fmt l -> Format.fprintf fmt "[%a]" (pp_list "," pp_cond) l)) l1

  let infi : t = [],[]
  let min1 : t = [[]],[]
  let zero : t = [],[[]]
                      
  (** The pretty printer for the type [cmp] *)
  let pp fmt c=
    Format.fprintf fmt "%s" (cmp_to_string c)

  let add_neutral = infi
  
  (** Addition operation (minimum) *)
  let plus : t -> t -> t =
    fun (sm1,eq1) (sm2,eq2) ->
      clean (ou sm1 sm2,ou eq1 eq2)

  (** Multiplication operation. *)
  let mult : t -> t -> t =
    fun (sm1,eq1) (sm2,eq2) ->
      clean (ou (ou (et sm1 sm2) (et sm1 eq2)) (et eq1 sm2),et eq1 eq2)

  (** Reduce by 1 a cmp *)
  let minus1 : t -> t =
    function
    | l1,l2 -> clean (l1@l2,[])

  (** Compute the minimum of a list *)
  let mini : t list -> t = fun l ->
    List.fold_left plus infi l
end

module Cmp_matrix = struct
  include Matrix(Cmp)

  (** Check if a matrix corresponds to a decreasing idempotent call. *)
  let decreasing : t -> Cmp.dnf = fun m ->
    assert (m.h = m.w);
    (* Only square matrices labeling a self-looping arrow need to be study *)
    let ll = ref [] in
    for k = 0 to m.h-1 do
      ll:=!ll@(fst m.tab.(k).(k))
    done;
    Format.printf "decreasing res : %a@." Cmp.pp_dnf (Cmp.useless_decr !ll);
    Cmp.useless_decr !ll
end

module Bool_matrix = struct 
  include
    Matrix(struct
        type t = bool         
        let pp          : t printer =
          fun fmt b -> Format.printf "%s" (if b then "T" else "F")
        let add_neutral : t = false
        let plus        : t -> t -> t = (||)
        let mult        : t -> t -> t = (&&)
      end)

  let diago : int -> t =
    fun n -> {h = n; w = n;
              tab = Array.init n (fun i -> Array.init n (fun j -> i=j))}
end

(** [cstr] are the constraints on type, coded by a triple, containing, the name of the constructor, the accessed argument and the name of the rule *)
let cstr : (string * int * string) list ref = ref []



