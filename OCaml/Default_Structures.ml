open List
open Utils
open Signatures


module Int_State : Formal_State_Sig =
struct 
  type state = State of int 
  let default_state = State(-1)
end

module Int_Labels : Label_Sig =
struct 
  type label = Label of int
  let default_label = Label(0)
end

module type Integer_Basic_Predicate_Sig =
sig
  
  include Symbolic_Predicate_Sig 
    with type label = int
    
  val make_in_singleton : int -> symbolic_predicate
  val make_out_singleton : int -> symbolic_predicate
    
end

module Integer_Basic_Predicate (*: Integer_Basic_Predicate_Sig*) =
struct

  module IntSet = Set.Make(struct type t = int let compare = Pervasives.compare end)
  type simple_integer_predicate = IN of IntSet.t | OUT of IntSet.t
  type symbolic_predicate = simple_integer_predicate
  type label = int
  
  let make_in_singleton i =
    let empty_pred = IntSet.empty in
    IN(IntSet.add i empty_pred)
    
  let make_out_singleton i =
    let empty_pred = IntSet.empty in
    OUT(IntSet.add i empty_pred)
  
  let evaluate predic a = match predic with 
    | IN(l) -> IntSet.mem a l
    | OUT(l) -> not (IntSet.mem a l)
    
  let conjunction predic1 predic2 = match (predic1,predic2) with
    | (IN(s1),IN(s2)) -> 
      IN(IntSet.inter s1 s2) 
    | (IN(s1),OUT(s2)) -> 
      IN(IntSet.diff s1 s2)
    | (OUT(s1),IN(s2)) ->
      IN(IntSet.diff s2 s1)
    | (OUT(s1),OUT(s2)) ->
      OUT(IntSet.union s1 s2)
      
  let negation = function
    | IN(s) -> OUT(s)
    | OUT(s) -> IN(s)
    
  let is_empty = function
    | IN(s) -> IntSet.is_empty s
    | _ -> false  
  
end

module Integer_Polynomials : Symbolic_Function_Sig = 
struct

  module Pred = Integer_Basic_Predicate
  open Pred
  
  type symbolic_function = Poly of int list
  type symbolic_predicate = Pred.symbolic_predicate
  type lin = int 
  type lout = int 
  
  let apply (Poly(l)) n = 
    let apply_poly n l = fold_right (fun b a -> a+n*b) l 0
    in Some(apply_poly n l)
    
  let is_empty predic _ = Pred.is_empty predic
  
  let is_singleton predic poly = match predic with
    | (IN(s)) -> 
      let results = fold_left
        (fun res_set value -> 
          let res = apply poly value in 
          match res with
            | Some x -> IntSet.add x res_set
            | None -> res_set
        )
        IntSet.empty
        (IntSet.elements s)
      in IntSet.cardinal results = 1
    | (OUT(s)) -> false
    
  let equivalent predic (Poly(l1)) (Poly(l2)) = match predic with
    | (IN(s)) ->
      fold_left
        (fun a value -> a && ((apply (Poly(l1)) value) = (apply (Poly(l2)) value)))
        true
        (IntSet.elements s)
    | (OUT(s)) -> l1 = l2
  
  let typecheck _ _ = true
  
  

end