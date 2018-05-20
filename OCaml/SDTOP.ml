open List
open Utils
open Signatures
open STree
open Default_Structures

module SDTOP : Symbolic_Transducer_Sig = 
functor (Lin : Label_Sig) ->
functor (Lout : Label_Sig) ->
functor (Sin : Ranked_Signature_Sig) ->
functor (Sout : Ranked_Signature_Sig) ->
functor (S : Formal_State_Sig) -> 
functor (Pred : Symbolic_Predicate_Sig) -> 
functor (Func : Symbolic_Function_Sig) ->
struct
  
  module Trees_in = Symbolic_Tree (Lin)
  module Trees_out = Symbolic_Tree (Lout)
      
  type label_in = Int_Labels.label
  type label_out = Int_Labels.label
  
  type tree_in = Trees_in.ranked_tree
  type tree_out = Trees_out.ranked_tree
  
  type state = S.state
  type symbolic_transducer = tree_in * tree_out
   
  let transduce trans tin = Trees_out.default_tree
    
end