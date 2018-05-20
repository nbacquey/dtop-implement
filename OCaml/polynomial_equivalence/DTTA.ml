open List
open Set
open Utils
open Signatures
open Default_Structures

module DTTA = 
functor (Sin : Ranked_Signature_Sig) ->
functor (States : Formal_State_Sig) -> 
struct

  module Trees_in = Ranked_Tree (Sin)
  open Trees_in
  
  type label = Sin.label
  type signature = Sin.signature
  
  type tree_in = Trees_in.ranked_tree
  
  type state = States.t  
  module State_set = Set.Make(States)
  
(* Automates Top-Down Déterministes *)

  type dtta_rule = (label * state) * state list

  type dtta = {
    signature : signature;
    states : State_set.t;
    initstate : state;
    rules : dtta_rule list
  }


  let rec check_dtta aut = 
    fold_left 
      (fun a ((symb,_),state_list) -> ((assoc symb aut.signature) = length state_list) && a) 
      true 
      aut.rules

  let run_automaton aut node = 
    let rec run_on_state state (Trees_in.Node(symb,children)) rules = 
      if (not (mem_assoc (symb,state) rules))
      then false
      else
        let node_state_list = combine children (assoc (symb,state) rules) in
        fold_left 
          (fun a (node,state_next) -> (run_on_state state_next node rules) && a)
          true
          node_state_list
    in 
    if (not (check_dtta aut)) then failwith "Automate mal défini" else 
    if (not (Trees_in.check_tree (aut.signature,node))) then failwith "Arbre non compatible" else
    run_on_state aut.initstate node aut.rules

  
let indexify_aut_rules idx = map
  ( fun ((symb,state),calls) ->
    let new_calls = map idx#get_index_of calls in
    ((symb,idx#get_index_of state),new_calls)
  )
  
(* Fonctions d'affichage *)
  
let print_DTTA_rule ((symb,state),calls) = 
  let rec print_state_list = function
      | [] -> ()
      | x::[] -> print_string (States.printable_value x)
      | x::xs -> print_string ((States.printable_value x)^",");
        print_state_list xs
    in
  print_string ("q"^(States.printable_value state)^"("^(Sin.printable_value symb)^") -> [");
  print_state_list calls;
  print_endline "]"
  
let print_DTTA aut =
  print_endline "Signature :";
  Sin.print aut.signature;
  print_endline "État initial :";
  print_endline ("q"^(States.printable_value aut.initstate));
  print_endline "Règles :";
  iter print_DTTA_rule aut.rules  

end