open Set
(* Signatures des modules *)


module type Formal_State_Sig =
sig 

  type t 
  val default_state : t
  val compare : t -> t -> int
  val printable_value : t -> string
  
end

module type Ranked_Signature_Sig =
sig 

  type label
  type signature = (label * int ) list
  val default_signature : signature
  val default_label : label
  val print : signature -> unit
  val printable_value : label -> string
  val check_sig : signature -> bool
  val compare : label -> label -> int
  
end


module type Tree_Sig = 
sig 

  type ranked_tree
  type label
  
  val default_tree : ranked_tree  
  val print : ranked_tree -> unit
  val check_tree : ('a * ranked_tree) -> bool
  
end

module type Context_Sig =
sig 

  type ranked_context 
  type label 
  type state 
  
  val default_context : ranked_context 
  val print : ranked_context -> unit
  
end

module type DTOP_Sig =
functor (Sin : Ranked_Signature_Sig ) ->
functor (Sout : Ranked_Signature_Sig ) ->
functor (States : Formal_State_Sig) ->
sig 
  
  type tree_in 
  type tree_out
  
  type dtop
  type state
  
  val transduce : (dtop -> tree_in -> tree_out)
  
  val print_DTOP : (dtop -> unit)
  
end 



