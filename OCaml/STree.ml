open List
open Utils
open Signatures

module Ranked_Tree = 
functor (L : Label_Sig) -> 
(struct
  
  type label = L.label
  type signature = (label * int) list 
  type ranked_tree = Node of (label * node list)
  
  let default_tree = Node(L.default_label,[])
    
end : Tree_Sig)

module Ranked_Context =
functor (L : Label_Sig) ->
functor (S : Formal_State_Sig) -> 
(struct 

  type label = L.label
  type state = S.state
  
  type ranked_context = Ctx_hole of (state * int) | Ctx_node of (label * ranked_context list)
  
  let default_context = Ctx_hole(S.default_state,0)
  
end : Context_Sig)