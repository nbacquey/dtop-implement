open List
open Utils
open Signatures
open Default_Structures
open DTOP
open DTTA
open Operations

module Equivalence =
functor (Sin : Ranked_Signature_Sig) ->
functor (Sout : Ranked_Signature_Sig) ->
functor (States_DTOP : Formal_State_Sig) ->
struct

module Operations = Operations (Sin) (Sout) (States_DTOP) (Int_State)
open Operations
open Operations.DTOP_Product

type dtop = dtop_before
type dtta = dtta_after

let (===) = Context_Couple.(===)

module Unification_Constraint =
struct
  type t = 
    State_Eq of Couple_State.t * Couple_State.t
    | Constraint of Couple_State.t * Context_Couple.ranked_context 
    | Error of Context_Couple.ranked_context * Context_Couple.ranked_context
    
  let print = function
    | Error(ctx1,ctx2) ->
      print_string "Error : can't match\n  ";
      Context_Couple.print ctx1;
      print_string "\n  with\n  ";
      Context_Couple.print ctx2;
      print_string "\n"
    | Constraint(q,ctx) ->
      print_string ("Constraint : "
      ^"q"^(Couple_State.printable_value q)
      ^" -> ");
      Context_Couple.print ctx;
      print_string "\n"
    | State_Eq(q1,q2) ->
      print_string ("Constraint : "
      ^"q"^(Couple_State.printable_value q1)
      ^" -> "
      ^"q"^(Couple_State.printable_value q2)
      ^"\n")    
end


(* Elimination des états constants *)

let simplify_constants (trans:dtop_product) = 
  let constants = ref [] in
  Couple_Set.iter 
    (fun state ->
      let rules_rhs = map
        (fun (_,rhs) -> rhs)
        (filter 
          (fun ((_,state2),_) -> state = state2)
          trans.rules 
        ) in
      match rules_rhs with
        | [] -> ()
        | hd::tl -> 
          if Context_Couple.is_constant hd then 
            let is_constant = fold_left
              (fun acc ctx -> acc && (hd === ctx))
              true
              tl in
            if is_constant 
            then constants := (state,hd)::(!constants)
    )
    trans.states;
    
    let rec replace_constants = function 
      | Context_Couple.Ctx_hole(state,childnum) ->
        if mem_assoc state !constants
        then assoc state !constants
        else Context_Couple.Ctx_hole(state,childnum)
      | Context_Couple.Ctx_node(symb,ctx_list) -> 
        Context_Couple.Ctx_node(symb, map replace_constants ctx_list) in
        
    let new_rules = map 
      (fun (lhs,rhs) -> (lhs, Context_Couple.factorize_context (replace_constants rhs)))
      (filter
        (fun ((_,state),_) -> not (mem_assoc state !constants))
        trans.rules
      )
    and new_states = 
      let (constant_states,_) = split !constants in
      Couple_Set.diff trans.states (Couple_Set.of_list constant_states) 
    and new_axiom = Context_Couple.factorize_context (replace_constants trans.axiom) in
      
    (({
      sigin = trans.sigin;
      sigout = trans.sigout;
      states = new_states;
      axiom = new_axiom;
      rules = new_rules
    }:dtop_product), (length !constants) > 0)
    
let remove_constants trans = 
  let new_couple = ref (trans,true) in
  while snd !new_couple
  do
    new_couple := simplify_constants (fst !new_couple)
  done;
  fst !new_couple
  
  
(* Fonctions de traitement des contraintes *)
open Context_Couple
open Unification_Constraint
  
let context_unification ctx1 ctx2 = 

  let check_soundness state childnum =
    let process_node = function
      | Ctx_node(_,_) -> true
      | Ctx_hole(state_i,childnum_i) -> 
        state <> state_i &&             (*no state recursion*)
        snd state = snd state_i &&      (*same domain*)
        childnum = childnum_i           (*call on same child number (because there are no constants left)*)
    in
    
    fold_dag process_node (&&)
  in
  
  let delete_calls =
    map_dag_leaves
    (fun leaf -> match leaf with
      | Ctx_node(_,_) -> failwith "Leaf mapping function applied on non-leave"
      | Ctx_hole(state,_) -> Ctx_hole(state,0)
    )
  in
  
  let process_context_pair ctx1 ctx2 = match (ctx1,ctx2) with
    | (Ctx_hole(state1,child1),Ctx_hole(state2,child2)) ->
      if child1 <> child2 
      then [Error(ctx1,ctx2)]
      else if state1 <> state2
        then [State_Eq(state1,state2)]
        else []
    | (Ctx_hole(state,childnum),ctx2) -> 
      if check_soundness state childnum ctx2 
      then 
        [Constraint(state,delete_calls ctx2)]
      else [Error(ctx1,ctx2)]
    | (ctx1,Ctx_hole(state,childnum)) -> 
      if check_soundness state childnum ctx1 
      then [Constraint(state,delete_calls ctx1)]
      else [Error(ctx2,ctx1)]
    | (Ctx_node(s1,_),Ctx_node(s2,_)) ->
      if s1 = s2
      then []
      else [Error(ctx1,ctx2)]
  in
  
  fold_dag2 process_context_pair (@) ctx1 ctx2
  
(* Instanciation des contraintes *)

let instantiate_constraints rules_table readable_symbols constraints =
  
  let instantiate_constraint (main_state,main_ctx) =
    let symbols = Hashtbl.find readable_symbols main_state in
    map
      (fun symb -> 
        let replacement = Hashtbl.find rules_table (symb,main_state) in
        let new_rhs = map_dag_leaves
          (fun ctx -> match ctx with
            |Ctx_node(_,_) -> ctx
            |Ctx_hole(state,_) -> Hashtbl.find rules_table (symb,state)          
          )
          main_ctx
        in
        (replacement,new_rhs)
      )
      symbols
  in
  fold_left
    ( fun acc cstr ->
      (instantiate_constraint cstr)@acc    
    )
    []
    constraints
    
  
let make_domain_wise trans = 
  let dom_aut = aut_canonical_numbering (minimize_automaton (DTOP_Before.make_DI_automaton trans)) in
  inspecter_times_transducer dom_aut trans

let test_equivalence trans1 trans2 = 
  let dom_aut1 = aut_canonical_numbering (minimize_automaton (DTOP_Before.make_DI_automaton trans1))
  and dom_aut2 = aut_canonical_numbering (minimize_automaton (DTOP_Before.make_DI_automaton trans2)) in
  
  if (dom_aut1 <> dom_aut2) then false else
  
  let trans1_wise = inspecter_times_transducer dom_aut1 trans1
  and trans2_wise = inspecter_times_transducer dom_aut1 trans2 in
  
  trans1_wise = trans2_wise
end