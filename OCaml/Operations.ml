open List
open Utils
open DTOP_Transducers
open DTT_Automata

(* Debug *)

let rec print_path = function 
  | [] -> print_newline()
  | (symb,num)::tail ->
    print_string (symb^(string_of_int num));
    print_path tail

(*Composition avec inspection de domaine*)

let compose_DI (aut1,trans1) (aut2,trans2) =
  let trans_dom2 = dtta_to_dtop aut2 in
  let trans_dom2_preim = compose_noDI trans1 trans_dom2 in
  let aut_dom2_preim = make_DI_automaton trans_dom2_preim in
  let aut3 =  minimize_automaton (automata_intersection aut1 aut_dom2_preim) in
  (aut3,compose_noDI trans1 trans2)

(*Forme normale d'un couple inspecteur + transducteur*)
  
(*Uniformisation : produit avec l'inspection*)
let inspecter_times_transducer aut trans = 
  Timer.start5();
  let idx = new indexator
  and agenda = new agenda
  and new_rules = ref [] in
  let rec complete_context aut_states = function
    | Ctx_hole(state,childnum) -> 
      let aut_state = nth aut_states (childnum -1) in
      agenda#add (aut_state,state);
      Ctx_hole(idx#get_index_of(aut_state,state),childnum)
    | Ctx_node(symb,ctx_list) -> 
      Ctx_node(symb,map (complete_context aut_states) ctx_list) in
  
  let new_axiom = complete_context [aut.initstate] trans.axiom in

  while not(agenda#is_empty())
  do
    let (aut_state,trans_state) = agenda#retrieve() in
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
        new_rules := ((symb,idx#get_index_of(aut_state,trans_state)),new_context)::(!new_rules);
      )
      possible_symbols;
      
    agenda#deliver (aut_state,trans_state)
  done;
  let result = {
    sigin = trans.sigin;
    sigout = trans.sigout;
    nbstates = idx#get_records_count();
    axiom = new_axiom;
    rules = !new_rules;
  } in
  Timer.stop5();
  result
  
(*Mise sous forme earliest*)

let rec context_intersection = function
  | (Ctx_node(symb1,ctx_list1),Ctx_node(symb2,ctx_list2)) when symb1 = symb2 ->
    let new_list = map2
      (fun ctx1 ctx2 -> context_intersection (ctx1,ctx2))
      ctx_list1
      ctx_list2 in
    Ctx_node(symb1,new_list)
  | _ -> bottom_ctx
  
let largest_common_prefix rule_list =
  match snd (split rule_list) with
  | [] -> bottom_ctx
  | ctx::tail ->
    fold_left
      (fun inter new_ctx -> context_intersection (inter,new_ctx))
      (context_intersection (ctx,ctx))
      tail
      
let replace_with_common_prefix (trans:dtop_transducer) state prefix = 
  let idx = new indexator in
  let new_rules = ref [] in
  
  let rec replace_prefix path childnum = function
    | Ctx_node(symb,ctx_list) -> 
      let i = ref 0 in
      Ctx_node(symb, map
        (fun ctx ->
          incr i;
          replace_prefix (path@[(symb,!i)]) childnum ctx
        )
        ctx_list
      )
    | bottom_ctx ->
      (*print_string ("état q_"^(string_of_int state)^" path  : ");
      print_path path; (*ALERT*)*)
      Ctx_hole(idx#get_index_of(state,path),childnum) 
  in
        
  let rec complete_context = function
    | Ctx_node(symb,ctx_list) ->
      Ctx_node(symb, map complete_context ctx_list)
    | Ctx_hole(old_state,childnum) ->
      if old_state <> state
      then
        Ctx_hole(idx#get_index_of(old_state,[]),childnum)
      else
        replace_prefix [] childnum prefix 
  in
      
  let replace_rule ((symb,old_state),old_ctx) =
    if old_state <> state
    then 
      new_rules := 
        (
          ((symb,idx#get_index_of(old_state,[])),complete_context old_ctx)
        )::!new_rules
    else begin
      let rec ctx_substract path = function
        | (Ctx_node(symb1,list1),Ctx_node(symb2,list2)) when symb1=symb2 ->
          let i = ref 0 in
          fold_left
          (fun ctx_list (ctx1,ctx2) ->
            incr i;
            ctx_list@(ctx_substract (path@[(symb1,!i)]) (ctx1,ctx2)) )  
          []
          (combine list1 list2)
        | (left_ctx,right_ctx) when right_ctx = bottom_ctx ->
          [(path,complete_context left_ctx)]
        | _ -> failwith "Substraction error" 
      in
      
      iter
        (fun (new_path,new_ctx) ->
          (*print_string ("état q_"^(string_of_int old_state)^" path  : ");
          print_path new_path; (*ALERT*)*)
          new_rules :=
            (
              ((symb,idx#get_index_of(old_state,new_path)), new_ctx)
            )::!new_rules
        )
        (ctx_substract [] (old_ctx,prefix)) 
    end
  in
  
  let new_axiom = complete_context trans.axiom in
  iter replace_rule trans.rules;
  
  {
    sigin=trans.sigin;
    sigout=trans.sigout;
    nbstates = idx#get_records_count();
    axiom = new_axiom;
    rules = !new_rules
  }
    

  

let make_earliest (trans:dtop_transducer) =
  Timer.start7();
  let old_trans = ref trans 
  and new_trans = ref trans
  and has_changed = ref true in
  
  let rec replace_state = function
    | [] -> ()
    | state::tail ->
      let restricted_rules = filter
        (fun ((_,s),_) -> (state = s))
        !old_trans.rules in
      let lcp = largest_common_prefix restricted_rules in
      (*print_ctx lcp;*)
      if (lcp = bottom_ctx)
      then
        replace_state tail
      else begin
        has_changed := true;
        new_trans := replace_with_common_prefix !old_trans state lcp  
      end
  in
        
  while !has_changed
  do
    old_trans := !new_trans;
    has_changed := false;    
    replace_state (range !old_trans.nbstates)
    
  done;
  Timer.stop7();
  !new_trans
  
(*Une étape de la fonction précédente : pour debug*)
let make_earlier (trans:dtop_transducer) = 
  let new_trans = ref trans in

  let rec replace_state = function
    | [] -> ()
    | state::tail ->
      let restricted_rules = filter
        (fun ((_,s),_) -> (state = s))
        trans.rules in
      let lcp = largest_common_prefix restricted_rules in
      if (lcp = bottom_ctx)
      then 
        replace_state tail
      else
        new_trans := replace_with_common_prefix trans state lcp  
  in
        
  replace_state (range trans.nbstates);    
  !new_trans
    
(* Numérotation/ordonnancement canonique des états *)
(*Automates*)
let aut_canonical_numbering aut = 
  Timer.start8();
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
      (fun ((symb1,_),_) ((symb2,_),_) -> String.compare symb1 symb2)
      rule_list in
    
    iter (fun (_,right) -> process_right_part right ) sorted_list;    
    agenda#deliver(current_state)
  done;
  
  let rename_right = map (fun a -> idx#get_index_of(a)) in
  
  let rename_rule ((symb,state),right) = 
    ((symb,idx#get_index_of state), rename_right right) in
    
  let new_rules = sort
    (fun ((symb1,state1),_) ((symb2,state2),_) ->
      let comp = compare state1 state2 in
      if comp = 0 
      then String.compare symb1 symb2
      else comp
    )
    (map rename_rule aut.rules) 
  in
  
  let result = {
    signature = sort (fun (s1,_) (s2,_) -> String.compare s1 s2) aut.signature;
    nbstates = idx#get_records_count();
    initstate = idx#get_index_of(aut.initstate);
    rules = new_rules
  } in
  Timer.stop8();
  result
  
(* DTOPs *)
let trans_canonical_numbering trans = 
  Timer.start9();
  let idx = new indexator
  and agenda = new agenda in
  
  let rec process_right_part = function
    | Ctx_node(symb,ctx_list) -> iter process_right_part ctx_list
    | Ctx_hole(state,_) -> 
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
      (fun ((symb1,_),_) ((symb2,_),_) -> String.compare symb1 symb2)
      rule_list in
    
    iter (fun (_,right) -> process_right_part right ) sorted_list;    
    agenda#deliver(current_state)
  done;
  
  let rec rename_right = function
    | Ctx_node(symb,ctx_list) -> Ctx_node(symb,map rename_right ctx_list)
    | Ctx_hole(state, childnum) -> Ctx_hole(idx#get_index_of state,childnum)
  in
  
  let rename_rule ((symb,state),right) = 
    ((symb,idx#get_index_of state), rename_right right) in
    
  let new_rules = sort
    (fun ((symb1,state1),_) ((symb2,state2),_) ->
      let comp = compare state1 state2 in
      if comp = 0 
      then String.compare symb1 symb2
      else comp
    )
    (map rename_rule trans.rules) 
  in
  
  let result = {
    sigin = sort (fun (s1,_) (s2,_) -> String.compare s1 s2) trans.sigin;
    sigout = sort (fun (s1,_) (s2,_) -> String.compare s1 s2) trans.sigout;
    nbstates = idx#get_records_count();
    axiom = rename_right trans.axiom;
    rules = new_rules
  } in
  Timer.stop9();
  result

(* Forme normale et égalité*)
let normal_form (aut,trans) =
  let aut_min = minimize_automaton (automata_intersection aut (make_DI_automaton trans)) in
  let trans_product = inspecter_times_transducer aut_min trans in
  let trans_earliest = minimize_transducer (make_earliest trans_product) in
  (aut_canonical_numbering aut,trans_canonical_numbering trans_earliest)
  
let trans_equality (aut1,trans1) (aut2,trans2) =
  (normal_form (aut1,trans1)) = (normal_form (aut2,trans2))