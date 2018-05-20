open List
open Set
open Utils
open Signatures
open Default_Structures
open DTTA


module DTOP =
functor (Sin : Ranked_Signature_Sig) ->
functor (Sout : Ranked_Signature_Sig) ->
functor (States : Formal_State_Sig) ->
struct

(* Définitions de types *)

  module Trees_in = Ranked_Tree (Sin)
  module Trees_out = Ranked_Tree (Sout)
  module Context_out = Ranked_Context (Sout) (States)
  
  open Trees_in
  open Trees_out
  open Context_out
      
  type label_in = Sin.label
  type label_out = Sout.label
  
  type tree_in = Trees_in.ranked_tree
  type tree_out = Trees_out.ranked_tree
  type ctx_out = Context_out.ranked_context
  
  type state = States.t  
  module State_set = Set.Make(States)
  
  type transducer_rule = (label_in * state) * ctx_out
  
  type dtop = {
    sigin:Sin.signature;
    sigout:Sout.signature;
    states:State_set.t;
    axiom:ctx_out;
    rules:transducer_rule list
  }
   

  exception NoRule of string

(* Fonctions d'affichage *)
    
  let print_DTOP_rule ((label,state),ctx) = 
    print_string ("q"^(States.printable_value state)^"("^(Sin.printable_value label)^") -> ");
    Context_out.print ctx;
    print_newline ()
  
  let print_DTOP trans =
    print_endline "Signature d'entrée :";
    Sin.print trans.sigin;
    print_endline "Signature de sortie :";
    Sout.print trans.sigout;
    print_endline "Axiome :";
    Context_out.print trans.axiom;
    print_newline ();
    print_endline "Règles :";
    iter print_DTOP_rule trans.rules

(* Fonctions de vérification *)

  let rec check_trans_rule sigin sigout states symbin statein= function
    | Context_out.Ctx_hole(stateout,chil) -> 
      State_set.mem statein states && State_set.mem stateout states 
      && mem_assoc symbin sigin && chil > 0 && chil <= assoc symbin sigin
    
    | Context_out.Ctx_node(symbout,children) -> 
      fold_left 
        (fun a b -> check_trans_rule sigin sigout states symbin statein b && a) 
        (mem (symbout, length children) sigout) 
        children
        
  let rec check_axiom sigout states = function
    | Context_out.Ctx_node(symbout,children) -> 
      fold_left 
        (fun a b -> check_axiom sigout states b && a) 
        (mem (symbout, length children) sigout) 
        children
        
    | Context_out.Ctx_hole(stateout,chil) -> 
      State_set.mem stateout states  && chil =1 
    

  let check_trans (trans:dtop) = 
    fold_left 
      (
        fun a b -> 
          let ((symb,state),context) = b in 
          a && (check_trans_rule trans.sigin trans.sigout trans.states symb state context)
      ) 
      (check_axiom trans.sigout trans.states trans.axiom) 
      trans.rules
    
  let rec compatible_signatures = function
    | ([],sig2) -> true
    | ((symb,arity)::tail,sig2) -> (mem (symb,arity) sig2) && compatible_signatures (tail,sig2)


(* Application d'un transducteur à un arbre *)

  let rec ctx_to_tree = function
    | Context_out.Ctx_node(symb,children) -> 
      Trees_out.Node(
        symb,
        fold_left (fun a b -> (ctx_to_tree b)::a) [] children
      )
    | Context_out.Ctx_hole(state,childnum) -> failwith "Context contains calls"
    

  let rec apply_rules rules = function 
    | (node,Context_out.Ctx_node(symbout,children)) -> 
      Context_out.Ctx_node(symbout, fold_left (fun a b -> (apply_rules rules (node,b))::a) [] children) 
    
    | (Trees_in.Node(symbin,childin),Context_out.Ctx_hole(state,child_number)) ->
      let Trees_in.Node(symbin,childin) = nth childin (child_number-1) in 
        if not (mem_assoc (symbin,state) rules) then failwith "Input is out of domain" else
        apply_rules rules (Trees_in.Node(symbin,childin), assoc (symbin,state) rules)  
    

  let transduce (trans:dtop) (tree:tree_in) = 
    if not ((Sin.check_sig trans.sigin) && (Sout.check_sig trans.sigout) && check_trans trans) 
    then failwith "Ill-defined transducer" else
    if not (Trees_in.check_tree (trans.sigin,tree) )
    then failwith "Ill-defined tree" else
    (ctx_to_tree (apply_rules trans.rules (Trees_in.Node(Sin.default_label,[tree]), trans.axiom)):tree_out)

(* Construction de l'automate reconnaissant le domaine d'un DTOP *)

  let rec browse_axiom = function
    | Context_out.Ctx_hole(state,_) -> [state]
    | Context_out.Ctx_node(_,children) -> fold_left (fun a b -> (browse_axiom b) @ a) [] children
  
  let rec browse_context = function
    | Context_out.Ctx_hole(state,childnum) -> [(childnum,state)]
    | Context_out.Ctx_node(_,children) -> fold_left (fun a b -> (browse_context b) @ a) [] children
  
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
      fold_left (fun a b -> intersect Sin.compare a b) symbols available_list in
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

  module Gen_DTTA = DTTA (Sin) (Int_State)
  open Gen_DTTA
  type dtta = Gen_DTTA.dtta
  
  let make_DI_automaton dtop = 
    let idx = new indexator 
    and agenda = new agenda in
    let init = get_init_state agenda idx dtop.axiom  
    and rules = make_DI_rules agenda idx dtop.sigin dtop.rules in
    let result : dtta = {
      signature = dtop.sigin;
      states = idx#get_indexes();
      initstate = init;
      rules = rules
    } in
    result
    
(* 
(* Composition de transducteurs SANS inspection *)

    
let trans_initial = ref null_trans

let fill_agenda agenda (state1,state2) =
  let rules = (!trans_initial).rules in
  iter
    (fun (symb,_) -> 
      if (mem_assoc (symb,state1) rules)
      then agenda#add ((state1,state2),symb)
    )
    (!trans_initial).sigin

let rec apply_rules_to_context agenda idx rules = function
  | (context,Ctx_node(symbout,children)) -> 
    Ctx_node(
      symbout, 
      fold_right 
        (fun b a -> (apply_rules_to_context agenda idx rules (context,b))::a) 
        children 
        []
    ) 
    
  | (Ctx_node(symb1,child1),Ctx_hole(state2,child_number2)) ->
    (let context = nth child1 (child_number2-1) in match context with
      | Ctx_node(symb1,child1) -> 
        if not (mem_assoc (symb1,state2) rules) 
        then raise ( NoRule ("Symbol "^symb1^" cannot be matched with state "^(string_of_int state2)) )
        else apply_rules_to_context agenda idx rules (Ctx_node(symb1,child1), assoc (symb1,state2) rules)
        
      | Ctx_hole(state1,child_number1) -> 
        fill_agenda agenda (state1,state2); 
        Ctx_hole(idx#get_index_of(state1,state2),child_number1)
    )
        
  | (Ctx_hole(_,_),Ctx_hole(_,_)) -> 
    failwith "Bad invocation of apply_rules_to_context : malformed context trees."
  (* should not happen if used properly *)

let make_composed_rules agenda idx rules1 rules2 =
  let rules = ref [] in
  while (not(agenda#is_empty()))
  do
    let ((state1,state2),symbol) = agenda#retrieve() in
    (try
      let rule = ((symbol, idx#get_index_of(state1,state2)), 
                  apply_rules_to_context 
                    agenda
                    idx
                    rules2 
                    (Ctx_node("0",[assoc (symbol,state1) rules1]),
                      Ctx_hole(state2,1)
                    )
                )
      in rules := rule::(!rules);
    with NoRule(a) -> ());
    agenda#deliver ((state1,state2),symbol)
  done;
  !rules

let compose_noDI (trans1:dtop_transducer) (trans2:dtop_transducer) = 
  Timer.start1();
  trans_initial := trans1;
  let idx = new indexator in
  let agenda = new agenda in
  if not(compatible_signatures (trans1.sigout,trans2.sigin)) 
  then failwith "Signatures are not compatible" else
  let sigin = trans1.sigin 
  and sigout = trans2.sigout 
  and axiom = apply_rules_to_context agenda idx trans2.rules (Ctx_node("0",[trans1.axiom]),trans2.axiom)
  and rules = make_composed_rules agenda idx trans1.rules trans2.rules
  and nbstates = idx#get_records_count() in
  Timer.stop1();
  {
    sigin = sigin ;
    sigout = sigout ; 
    nbstates = nbstates ; 
    axiom = axiom ; 
    rules = rules
  }

(* Fonctions diverses pour transducteurs *)
  
let rec indexify_ctx idx = function
  | Ctx_node(symb, ctx_list) -> Ctx_node(symb, map (indexify_ctx idx) ctx_list)
  | Ctx_hole(state, childnum) -> Ctx_hole(idx#get_index_of state,childnum)
  
let indexify_trans_rules idx = map
  ( fun ((symb,state),ctx) ->
    ((symb,idx#get_index_of state),indexify_ctx idx ctx)
  )
  
(* Minimisation de DTOPs *)

let rec extract_states = function
  | Ctx_node(_, ctx_list) -> fold_left
    (fun a b -> a @ (extract_states b))
    []
    ctx_list
  | Ctx_hole(state,_) -> [state]
      
let trans_access_checker trans = 
  let accessible_states = ref (extract_states trans.axiom)
  and old = ref [] in
  while(!accessible_states <> !old)
  do
    old := !accessible_states;
    accessible_states := fold_left
      (fun a ((_,state),ctx) -> 
        if mem state !accessible_states
        then
          extract_states ctx @ a
        else
          a
      )
      !old
      trans.rules;
    accessible_states := sort_uniq compare !accessible_states
  done;
  (fun ((_,a),_) -> mem a !accessible_states)    

let trans_remove_unaccessible trans = 
  let idx = new indexator 
  and checker = trans_access_checker trans in
  let new_rules = indexify_trans_rules idx ( filter checker trans.rules ) 
  and axiom = indexify_ctx idx trans.axiom in
  {
    sigin = trans.sigin;
    sigout = trans.sigout;
    axiom;
    nbstates = idx#get_records_count();
    rules=new_rules
  }
  

let rec get_partition_of elt = function
  | [] -> failwith "element not in partition"
  | x::xs -> if mem elt x then x else get_partition_of elt xs

let transform_state idx partition state =
  idx#get_index_of (get_partition_of state partition)
  
let rec transform_ctx idx partition = function
  | Ctx_node(symb,ctx_list) -> Ctx_node(symb, map (transform_ctx idx partition) ctx_list)
  | Ctx_hole(state,child_num) -> Ctx_hole(transform_state idx partition state,child_num)
  
let replace_trans_rule idx partition ((symb,state),ctx) = 
  ((symb,transform_state idx partition state),transform_ctx idx partition ctx)
  
let rebuild_transducer partition trans = 
  let idx = new indexator in
  {
    sigin = trans.sigin;
    sigout = trans.sigout;
    nbstates = length partition;
    axiom = transform_ctx idx partition trans.axiom;
    rules =  nub (map (replace_trans_rule idx partition) trans.rules)
  }

let trans_states_equality state1 state2 partition rules =
  let rec compare_with_partition ctx1 ctx2 = match (ctx1,ctx2) with
    | (Ctx_node(symb1,ctx_list1),Ctx_node(symb2,ctx_list2)) ->
      if (length ctx_list1 <> length ctx_list2) then false else
      fold_left
        (fun a (sub_ctx1,sub_ctx2) -> a && (compare_with_partition sub_ctx1 sub_ctx2))
        (symb1=symb2)
        (combine ctx_list1 ctx_list2)
    | (Ctx_hole(state1,childnum1),Ctx_hole(state2,childnum2)) ->
      (childnum1 = childnum2) && 
      ((get_partition_of state1 partition)=(get_partition_of state2 partition))
    | _ -> false
      
  and compare_rules ((symb1,_),_) ((symb2,_),_) =
    String.compare symb1 symb2
  in
  
  let process_rules state = filter (fun ((_,state_tmp),_) -> (state = state_tmp)) rules
  in
  
  let rules1 = sort compare_rules (process_rules state1 )
  and rules2 = sort compare_rules (process_rules state2 )
  in
  if (length rules1 <> length rules2) then false else
  fold_left 
    (fun a (((symb1,_),ctx1),((symb2,_),ctx2)) -> 
      a && (symb1=symb2) && (compare_with_partition ctx1 ctx2)
    )
    true
    (combine rules1 rules2)
    
let rec trans_cram_state state partition rules = function
  | [] -> [[state]]
  | ([])::tail -> failwith "Sub-partition should not contain empty elements"
  | (x::xs)::tail ->
    if (trans_states_equality state x partition rules)
    then (state::(x::xs))::tail
    else (x::xs)::(trans_cram_state state partition rules tail)

let trans_split_state_set states rules partition =
  let remain = ref states
  and processed = ref [] in
  while (!remain <> [])
  do
    let state = hd !remain in
    remain := tl !remain;
    processed := trans_cram_state state partition rules !processed;
  done;
  !processed  

let trans_partition_states trans = 
  let partition = ref [range trans.nbstates] 
  and continue = ref true in
  while (!continue)
  do
    let l1 = length !partition in
    partition := fold_left
      (fun a b -> (trans_split_state_set b trans.rules !partition)@a)
      []
      !partition;
    continue :=  (l1 <> length !partition);
  done;
  !partition

let minimize_transducer trans = 
  Timer.start6();
  let partition = trans_partition_states trans in
  let trans_rebuild = rebuild_transducer partition trans in
  let result = trans_remove_unaccessible trans_rebuild in
  Timer.stop6();
  result
*)  
end

