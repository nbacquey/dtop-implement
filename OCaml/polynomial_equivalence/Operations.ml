open List
open Utils
open Signatures
open Default_Structures
open DTOP
open DTTA

module Operations =
functor (Sin : Ranked_Signature_Sig) ->
functor (Sout : Ranked_Signature_Sig) ->
functor (States_DTOP : Formal_State_Sig) ->
functor (States_DTTA : Formal_State_Sig) ->
struct

  module Trees_in = Ranked_Tree (Sin)
  module Trees_out = Ranked_Tree (Sout)
  module Context_Before = Ranked_Context (Sout) (States_DTOP)
  module Context_After = Ranked_Context (Sout) (Int_State)
  module Context_Ident = Ranked_Context (Sin) (States_DTTA)
  
  open Trees_in
  open Trees_out
  open Context_Before  
  open Context_After
  
  
  module DTOP_Before = DTOP (Sin) (Sout) (States_DTOP)
  open DTOP_Before
  type dtop_before = DTOP_Before.dtop
  
  module DTOP_After = DTOP (Sin) (Sout) (Int_State)
  open DTOP_After
  type dtop_after = DTOP_After.dtop
  
  module DTTA_Before = DTTA (Sin) (States_DTTA)
  open DTTA_Before
  type dtta_before = DTTA_Before.dtta
  
  module DTTA_After = DTTA (Sin) (Int_State)
  open DTTA_After
  type dtta_after = DTTA_After.dtta
  
  module DTOP_Ident = DTOP (Sin) (Sin) (States_DTTA)
  open DTOP_Ident
  type dtop_ident = DTOP_Ident.dtop
  
  module Couple_State = Couple_State (States_DTOP) (States_DTTA)
  module DTOP_Product = DTOP (Sin) (Sout) (Couple_State)
  open DTOP_Product
  type dtop_product = DTOP_Product.dtop
  
  module Context_Couple = Ranked_Context (Sout) (Couple_State)
  open Context_Couple
  
  module Couple_Set = Set.Make(Couple_State)
  

(*Forme normale d'un couple inspecteur + transducteur*)
  

(*Uniformisation : produit avec l'inspection*)
let inspecter_times_transducer (aut:dtta_before) (trans:dtop_before) = 
  (*let idx = new indexator*)
  let agenda = new agenda
  and new_rules = ref [] in
  let rec complete_context aut_states = function
    | Context_Before.Ctx_hole(state,childnum) -> 
      let aut_state = nth aut_states (childnum -1) in
      agenda#add (state,aut_state);
      Context_Couple.Ctx_hole((state,aut_state),childnum)
    | Context_Before.Ctx_node(symb,ctx_list) -> 
      Context_Couple.Ctx_node(symb,map (complete_context aut_states) ctx_list) in
  
  let new_axiom = complete_context [aut.initstate] (trans:dtop_before).axiom in

  while not(agenda#is_empty())
  do
    let (trans_state,aut_state) = agenda#retrieve() in
    let possible_symbols = filter 
      (fun symb -> 
        (mem_assoc (symb,aut_state) aut.rules) && 
        (mem_assoc (symb,trans_state) trans.rules) 
      )
      (map 
        (fun (symb,_) -> symb)
        trans.sigin
      ) in
    
    iter 
      (fun symb ->
        let aut_states = assoc (symb,aut_state) aut.rules in
        let new_context = complete_context aut_states (assoc (symb,trans_state) trans.rules) in
        new_rules := ((symb,(trans_state,aut_state)),new_context)::(!new_rules);
      )
      possible_symbols;
      
    agenda#deliver (trans_state,aut_state)
  done;
  let result : dtop_product = {
    sigin = trans.sigin;
    sigout = trans.sigout;
    states = Couple_Set.of_list (agenda#all_work());
    axiom = new_axiom;
    rules = !new_rules;
  } in
  result

(* Numérotation/ordonnancement canonique des états *)
(*Automates*)
let aut_canonical_numbering (aut:dtta_before) = 
  let idx = new indexator
  and agenda = new agenda in
  
  let rec process_right_part = function
    | [] -> ()
    | x::xs -> 
      agenda#add(x,idx#get_index_of x); 
      process_right_part xs
  in
  
  process_right_part [aut.initstate];
  
  while(not (agenda#is_empty()))
  do
    let current_state = agenda#retrieve() in
    let rule_list = filter
      (fun ((_,state),_) -> state = fst current_state)
      aut.rules in
    let sorted_list = sort
      (fun ((symb1,_),_) ((symb2,_),_) -> Sin.compare symb1 symb2)
      rule_list in
    
    iter (fun (_,right) -> process_right_part right ) sorted_list;    
    agenda#deliver(current_state)
  done;
  
  let rename_right = map (fun a -> idx#get_index_of(a)) in
  
  let rename_rule ((symb,state),right) = 
    ((symb,idx#get_index_of state), rename_right right) in
    
  let new_rules = sort
    (fun ((symb1,state1),_) ((symb2,state2),_) ->
      let comp = Int_State.compare state1 state2 in
      if comp = 0 
      then Sin.compare symb1 symb2
      else comp
    )
    (map rename_rule aut.rules) 
  in
  
  let result = {
    signature = sort (fun (s1,_) (s2,_) -> Sin.compare s1 s2) aut.signature;
    states = idx#get_indexes();
    initstate = idx#get_index_of(aut.initstate);
    rules = new_rules
  } in
  (result:dtta_after)
  
(* DTOPs *)
let trans_canonical_numbering (trans:dtop_before) = 
  let idx = new indexator
  and agenda = new agenda in
  
  let rec process_right_part = function
    | Context_Before.Ctx_node(symb,ctx_list) -> iter process_right_part ctx_list
    | Context_Before.Ctx_hole(state,_) -> 
      agenda#add(state,idx#get_index_of state)
  in
  
  process_right_part trans.axiom;
  
  while(not (agenda#is_empty()))
  do
    let current_state = agenda#retrieve() in
    let rule_list = filter
      (fun ((_,state),_) -> state = fst current_state)
      trans.rules in
    let sorted_list = sort
      (fun ((symb1,_),_) ((symb2,_),_) -> Sin.compare symb1 symb2)
      rule_list in
    
    iter (fun (_,right) -> process_right_part right ) sorted_list;    
    agenda#deliver(current_state)
  done;
  
  let rec rename_right = function
    | Context_Before.Ctx_node(symb,ctx_list) -> Context_After.Ctx_node(symb,map rename_right ctx_list)
    | Context_Before.Ctx_hole(state, childnum) -> Context_After.Ctx_hole(idx#get_index_of state,childnum)
  in
  
  let rename_rule ((symb,state),right) = 
    ((symb,idx#get_index_of state), rename_right right) in
    
  let new_rules = sort
    (fun ((symb1,state1),_) ((symb2,state2),_) ->
      let comp = Int_State.compare state1 state2 in
      if comp = 0 
      then Sin.compare symb1 symb2
      else comp
    )
    (map rename_rule trans.rules) 
  in
  
  ({
    sigin = sort (fun (s1,_) (s2,_) -> Sin.compare s1 s2) trans.sigin;
    sigout = sort (fun (s1,_) (s2,_) -> Sout.compare s1 s2) trans.sigout;
    states = idx#get_indexes();
    axiom = rename_right trans.axiom;
    rules = new_rules
  }:dtop_after)
  
(* Minimisation de DTTA *)

  let access_checker aut = 
    let accessible_states = ref [aut.initstate] 
    and old = ref [] in
    while(!accessible_states <> !old)
    do
      old := !accessible_states;
      accessible_states := fold_left
        (fun a ((_,state),calls) -> 
          if mem state !accessible_states
          then
            calls @ a
          else
            a
        )
        !old
        aut.rules;
      accessible_states := sort_uniq compare !accessible_states
    done;
    (fun ((_,a),_) -> mem a !accessible_states)    

  let remove_unaccessible aut = 
    let idx = new indexator 
    and checker = access_checker aut in
    let new_rules = indexify_aut_rules idx ( filter checker aut.rules ) 
    and initstate = idx#get_index_of aut.initstate in
    ({
      signature = aut.signature;
      initstate;
      states = idx#get_indexes();
      rules=new_rules
    }:dtta_after)
  

  let rec get_partition_of elt = function
    | [] -> failwith "element not in partition"
    | x::xs -> if mem elt x then x else get_partition_of elt xs 
  
  let replace_rule old_to_new ((symb,state),calls) = 
    (
      (symb,assoc state old_to_new ),
      map (fun called_state -> assoc called_state old_to_new) calls
    )
  
  let rebuild_automaton partition (auto:dtta_before) = 
    let idx = new indexator in
    let old_to_new = map
      (fun state -> (state,idx#get_index_of (get_partition_of state partition)))
      (DTTA_Before.State_set.elements auto.states)
      in
    ({
      signature = auto.signature;
      states = idx#get_indexes();
      initstate = assoc auto.initstate old_to_new ;
      rules =  nub (map (replace_rule old_to_new) auto.rules)
    }:dtta_after)

  let states_equality state1 state2 part_rules =

    let process_rules state = 
      map
        (fun ((symb,_),statelist) -> 
          ((symb,0),statelist)
        )
        (assoc state part_rules)
      
    and compare_rules ((symb1,_),_) ((symb2,_),_) =
      Sin.compare symb1 symb2
    in
  
    let rules1 = sort compare_rules (process_rules state1)
    and rules2 = sort compare_rules (process_rules state2) in
    rules1=rules2
    
  let rec cram_state state part_rules = function
    | [] -> [[state]]
    | ([])::tail -> failwith "Sub-partition should not contain empty elements"
    | (x::xs)::tail ->
      if (states_equality state x part_rules)
      then (state::(x::xs))::tail
      else (x::xs)::(cram_state state part_rules tail)

  let split_state_set states part_rules =
    let remain = ref states
    and processed = ref [] in
    while (!remain <> [])
    do
      let state = hd !remain in
      remain := tl !remain;
      processed := cram_state state part_rules !processed;
    done;
    !processed  

  let partition_states (auto:dtta_before) = 
    let state_list = DTTA_Before.State_set.elements auto.states in
    let partition = ref [state_list] 
    and continue = ref true in
    
    let rules_by_state = map
      (fun state ->
        (state,filter (fun ((_,state_tmp),_) -> state_tmp = state) auto.rules)
      )
      (state_list) in
  
    while (!continue)
    do
      let l1 = length !partition in
      let state_to_part = map
        (fun state -> (state,get_partition_of state !partition)) 
        state_list in
      
      let part_rules = map
        (fun (state,rules_list) ->
          (state,map 
            (fun (symb,statelist) -> (symb,map 
              (fun q -> assoc q state_to_part)
              statelist)
            ) 
            rules_list
          )
        )
        rules_by_state in
    
      partition := fold_left
        (fun a b -> (split_state_set b  part_rules )@a)
        []
        !partition;
      continue :=  (l1 <> length !partition);
    done;
    !partition

  let minimize_automaton (auto:dtta_before) = 
    let partition = partition_states auto in
    let aut_rebuild = rebuild_automaton partition auto in
    let result = remove_unaccessible aut_rebuild in
    result

(* Intersection d'automates *)
  
  let make_intersection_rules rules1 rules2 =
    let rec make_product_rule ((symb1,s1),calls1) = function
      | ((symb2,s2),calls2)::tail when symb1 = symb2 ->
        ((symb1,(s1,s2)), combine calls1 calls2)::(make_product_rule ((symb1,s1),calls1) tail)
      | _::tail ->
        make_product_rule ((symb1,s1),calls1) tail
      | [] -> []

    in fold_left
      (fun a b -> (make_product_rule b rules2)@a)
      []
      rules1

  let equivalent_signatures sig1 sig2 =
    let compare_symb (symb1,_) (symb2,_) =
      Sin.compare symb1 symb2 in
    sort compare_symb sig1 = sort compare_symb sig2
  
  let automata_intersection aut1 aut2 =
    if (not(equivalent_signatures aut1.signature aut2.signature))
    then
      failwith "Different signatures can't be intersected.";
    let idx = new indexator
    and intersection_rules = make_intersection_rules aut1.rules aut2.rules in
    let rules = indexify_aut_rules idx intersection_rules in
    let initstate = idx#get_index_of (aut1.initstate,aut2.initstate) in
    let states = idx#get_indexes() in
    ({
      signature = aut1.signature;
      initstate;
      states;
      rules
    }:dtta_after)
  
(* transformation DTTA -> DTOP identité *)

  let dtta_to_dtop (dtta:dtta_before) = 
    let rec transform_rule ((symb,state),calls_list) = 
      let i = ref 0 in
      ((symb,state), Context_Ident.Ctx_node(
        symb,
        (map (fun call -> incr i; Context_Ident.Ctx_hole(call,!i)) calls_list)
        )
      ) in
    ({
      sigin = dtta.signature;
      sigout = dtta.signature;
      states = dtta.states;
      axiom = Context_Ident.Ctx_hole(dtta.initstate,1);
      rules = map transform_rule dtta.rules
    }:dtop_ident)
  
end
