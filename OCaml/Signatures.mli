
(* Signatures des modules *)

module type Label_Sig =
sig

  type label
  val default_label : label
  
end

module type Formal_State_Sig =
sig 

  type state 
  val default_state : state
  
end

module type Ranked_Signature_Sig =
sig 

  type label
  type signature 
  val default_signature : signature
  
end

module type Symbolic_Predicate_Sig = 
sig
  
  type symbolic_predicate
  type label 
  
  val evaluate : (symbolic_predicate ->  label -> bool)
  val conjunction : (symbolic_predicate -> symbolic_predicate -> symbolic_predicate )
  val negation : (symbolic_predicate -> symbolic_predicate )
  val is_empty : (symbolic_predicate -> bool)
  
end

module type Symbolic_Function_Sig = 
sig

  type symbolic_function
  type symbolic_predicate
  type lin 
  type lout 
  
  val apply : (symbolic_function -> lin -> (lout) option )
  
  val is_empty : 
    (symbolic_predicate -> symbolic_function -> bool)
  val is_singleton : 
    (symbolic_predicate -> symbolic_function -> bool)
  val equivalent : 
    (symbolic_predicate -> symbolic_function -> symbolic_function -> bool)
  val typecheck : (symbolic_function -> lin -> bool)
  
end

module type Symbolic_Tree_Sig = 
sig 

  type ranked_tree
  type label
  
  val default_tree : ranked_tree  
  
end

module type Symbolic_Term_Sig =
sig 

  type ranked_term 
  type label 
  type state 
  
  val default_term : ranked_term 
  
end

module type Symbolic_Transducer_Sig =
functor (Lin : Label_Sig) ->
functor (Lout : Label_Sig) ->
functor (Sin : Ranked_Signature_Sig with type label = Lin.label) ->
functor (Sout : Ranked_Signature_Sig with type label = Lout.label) ->
functor (S : Formal_State_Sig) ->
functor (Pred : Symbolic_Predicate_Sig with type label = Lin.label) ->
functor (Func : Symbolic_Function_Sig with type lin = Lin.label and type lout = Lout.label) ->
sig 
  
  type tree_in 
  type tree_out
  
  type symbolic_transducer
  type state
  
  val transduce : (symbolic_transducer -> tree_in -> tree_out)
  
end 



