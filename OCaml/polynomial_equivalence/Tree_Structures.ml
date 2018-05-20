open List
open Utils
open Signatures

module Ranked_Tree = 
functor (Sig : Ranked_Signature_Sig) -> 
struct
  
  type label = Sig.label
  type ranked_tree = Node of (label * ranked_tree list)
  
  let default_tree = 
    let l = Sig.default_label in
    Node(l,[])
    
  let rec check_tree (signature,Node(name,children)) =  
  fold_left 
    (fun a b -> a && (check_tree (signature,b)) ) 
    (mem (name,length children) signature) 
    children
    
  let rec print (Node(label,tree_list)) = 
    print_string (Sig.printable_value label);
    let rec print_list = function
      | [] -> ()
      | x::[] -> print x
      | x::xs -> print x;
        print_string ",";
        print_list xs
    in
    
    if (length tree_list) > 0
    then begin
      print_string "(";
      print_list tree_list;
      print_string ")"
    end
    
    
end

module Ranked_Context =
functor (Sig : Ranked_Signature_Sig) ->
functor (States : Formal_State_Sig) -> 
struct 

  type label = Sig.label
  type state = States.t
  
  type ranked_context = Ctx_hole of (state * int) | Ctx_node of (label * ranked_context list)
  
  let default_context = 
    let l = Sig.default_label in
    Ctx_node(l,[])
    
  let rec print = function
  | Ctx_node(label,ctx_list) -> 
    print_string (Sig.printable_value label);
    let rec print_ctx_list = function
      | [] -> ()
      | x::[] -> print x
      | x::xs -> print x;
        print_string ",";
        print_ctx_list xs
    in
    
    if (length ctx_list) > 0
    then begin
      print_string "(";
      print_ctx_list ctx_list;
      print_string ")"
    end
    
  | Ctx_hole(state,childnum) ->
    print_string ("q"^(States.printable_value state)^"(x"^(string_of_int childnum)^")")
    
end