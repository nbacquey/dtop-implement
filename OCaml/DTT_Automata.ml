open List
open Utils
open DTOP_Transducers

(* Automates Top-Down Déterministes *)

type dtta_rule = (string * int) * int list

type dtt_automaton = {
  signature : signature;
  nbstates : int;
  initstate : int;
  rules : dtta_rule list
}

let null_dttrule = (("0",1),[])

let null_dtta = {
  signature = null_sig;
  nbstates = 1;
  initstate = 1;
  rules = []
}

let rec check_dtta aut = 
  fold_left 
    (fun a ((symb,_),state_list) -> ((assoc symb aut.signature) = length state_list) && a) 
    true 
    aut.rules

let run_automaton aut (signature,node) = 
  let rec run_on_state state (Node(symb,children)) rules = 
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
  if (not (check_tree (signature,node))) then failwith "Arbre mal défini" else
  run_on_state aut.initstate node aut.rules
   
let equivalent_signatures sig1 sig2 =
  let compare_symb (symb1,_) (symb2,_) =
    String.compare symb1 symb2 in
  sort compare_symb sig1 = sort compare_symb sig2
  
let indexify_aut_rules idx = map
  ( fun ((symb,state),calls) ->
    let new_calls = map idx#get_index_of calls in
    ((symb,idx#get_index_of state),new_calls)
  )
  
(* Fonctions d'affichage *)

let print_symbol (symb,arity) =
  print_endline ("("^symb^","^(string_of_int arity)^")")
  
let print_DTTA_rule ((symb,state),calls) = 
  let rec print_int_list = function
      | [] -> ()
      | x::[] -> print_string (string_of_int x)
      | x::xs -> print_string ((string_of_int x)^",");
        print_int_list xs
    in
  print_string ("q"^(string_of_int state)^"("^symb^") -> [");
  print_int_list calls;
  print_endline "]"
  
let print_DTTA aut =
  print_endline "Signature :";
  iter print_symbol aut.signature;
  print_endline "État initial :";
  print_endline ("q"^(string_of_int aut.initstate));
  print_endline "Règles :";
  iter print_DTTA_rule aut.rules
   
(* Construction de l'automate reconnaissant le domaine d'un DTOP *)
   
let rec browse_axiom = function
  | Ctx_hole(state,_) -> [state]
  | Ctx_node(_,children) -> fold_left (fun a b -> (browse_axiom b) @ a) [] children
  
let rec browse_context = function
  | Ctx_hole(state,childnum) -> [(childnum,state)]
  | Ctx_node(_,children) -> fold_left (fun a b -> (browse_context b) @ a) [] children
  
let process_state_list agenda l=
  let lsort = sort_uniq compare l in
  agenda#add lsort;
  lsort
  
let make_righthand_side_rule agenda idx arity couple_list = 
  let tbl = Hashtbl.create arity in
  iter (fun (childnum,state) -> Hashtbl.add tbl childnum state) couple_list;
  let vect = Array.init arity (fun i -> (process_state_list agenda (Hashtbl.find_all tbl (i+1)))) in
  let state_list_list = Array.to_list vect in
  map (fun a -> idx#get_index_of a) state_list_list  
  
  
let get_init_state agenda idx axiom =
  let l = (browse_axiom axiom) in
  let lsort = sort_uniq compare l in
  agenda#add lsort;
  idx#get_index_of lsort 
    
let make_DI_rule agenda idx signature dtop_rules state_list =
  let symbols = 
    map (fun (symb,arity) -> symb) signature 
  and filter_rules state = 
    filter (fun ((_,pre_state),_) -> (pre_state = state)) in
  let make_available_list state = 
    map (fun ((symb,_),_) -> symb) (filter_rules state dtop_rules) in
  let available_list = 
    map (fun state -> make_available_list state) state_list in
  let available_symbols = 
    fold_left (fun a b -> intersect String.compare a b) symbols available_list in
  let merge_state_couples symb = 
    fold_left (fun a b -> (browse_context (assoc (symb,b) dtop_rules)) @ a) [] state_list in
  map 
    (
      fun symb ->(
        (symb,idx#get_index_of state_list),
        make_righthand_side_rule agenda idx (assoc symb signature) (merge_state_couples symb)
      )
    )
    available_symbols
    
let make_DI_rules agenda idx signature dtop_rules =
  let rules = ref [] in
  while (not(agenda#is_empty()))
  do
    let state_list = agenda#retrieve() in
    let rule = make_DI_rule agenda idx signature dtop_rules state_list
    in rules := rule@(!rules);
    agenda#deliver (state_list)
  done;
  !rules

let make_DI_automaton dtop = 
  Timer.start2();
  let idx = new indexator 
  and agenda = new agenda in
  let init = get_init_state agenda idx dtop.axiom  
  and rules = make_DI_rules agenda idx dtop.sigin dtop.rules in
  let result = {
    signature = dtop.sigin;
    nbstates = idx#get_records_count();
    initstate = init;
    rules = rules
  } in
  Timer.stop2();
  result


(* Minimisation d'automate DTT *)

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
  {
    signature = aut.signature;
    initstate;
    nbstates = idx#get_records_count();
    rules=new_rules
  }
  

let rec get_partition_of elt = function
  | [] -> failwith "element not in partition"
  | x::xs -> if mem elt x then x else get_partition_of elt xs 
  
let replace_rule old_to_new ((symb,state),calls) = 
  (
    (symb,Array.get old_to_new (state-1)),
    map (fun called_state -> Array.get old_to_new (called_state-1)) calls
  )
  
let rebuild_automaton partition auto = 
  let idx = new indexator in
  let old_to_new = Array.init
    auto.nbstates
    (fun state -> idx#get_index_of (get_partition_of (state+1) partition)) in
    
  {
    signature = auto.signature;
    nbstates = length partition;
    initstate = Array.get old_to_new (auto.initstate-1);
    rules =  nub (map (replace_rule old_to_new) auto.rules)
  }

let states_equality state1 state2 part_rules =

  let process_rules state = 
    map
      (fun ((symb,_),statelist) -> 
        ((symb,0),statelist)
      )
      (Array.get part_rules (state-1))
      
  and compare_rules ((symb1,_),_) ((symb2,_),_) =
    String.compare symb1 symb2
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

let partition_states auto = 
  let partition = ref [range auto.nbstates] 
  and continue = ref true in
  
  let rules_by_state = map
    (fun state ->
      filter (fun ((_,state_tmp),_) -> state_tmp = state) auto.rules
    )
    (range3 1 auto.nbstates 1) in
  
  while (!continue)
  do
    let l1 = length !partition in
    let state_to_part = Array.init
      auto.nbstates
      (fun state -> get_partition_of (state+1) !partition) in
      
    let part_rules = map
      (fun rules_list ->
        map 
          (fun (a,statelist) -> (a,map 
            (fun q -> Array.get state_to_part (q-1))
            statelist)
          ) 
          rules_list
      )
      rules_by_state in
    
    partition := fold_left
      (fun a b -> (split_state_set b (Array.of_list part_rules) )@a)
      []
      !partition;
    continue :=  (l1 <> length !partition);
  done;
  !partition

let minimize_automaton auto = 
  Timer.start3();
  let partition = partition_states auto in
  let aut_rebuild = rebuild_automaton partition auto in
  let result = remove_unaccessible aut_rebuild in
  Timer.stop3();
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

let automata_intersection aut1 aut2 =
  Timer.start4();
  if (not(equivalent_signatures aut1.signature aut2.signature))
  then
    failwith "Different signatures can't be intersected.";
  let idx = new indexator
  and intersection_rules = make_intersection_rules aut1.rules aut2.rules in
  let rules = indexify_aut_rules idx intersection_rules in
  let initstate = idx#get_index_of (aut1.initstate,aut2.initstate) in
  let nbstates = idx#get_records_count() in
  let result = {
    signature = aut1.signature;
    initstate;
    nbstates;
    rules
  } in
  Timer.stop4();
  result
  
(* transformation DTTA -> DTOP identité *)

let dtta_to_dtop dtta = 
  Timer.start0();
  let rec transform_rule ((symb,state),calls_list) = 
    let i = ref 0 in
    ((symb,state), Ctx_node(
      symb,
      (map (fun call -> incr i; Ctx_hole(call,!i)) calls_list)
      )
    ) in
  let result = {
    sigin = dtta.signature;
    sigout = dtta.signature;
    nbstates = dtta.nbstates;
    axiom = Ctx_hole(dtta.initstate,1);
    rules = map transform_rule dtta.rules
  } in
  Timer.stop0();
  result
