open List
open Utils

(* Définitions de types *)

type signature = (string * int) list

type node = Node of string * node list

type ranked_tree = signature * node 

type context_node = Ctx_hole of int * int | Ctx_node of string * context_node list 
(* Ctx_hole of state * child_number *)

type transducer_rule = (string * int) * context_node

type dtop_transducer = {
  sigin:signature ;
  sigout:signature ; 
  nbstates:int ; 
  axiom:context_node ; 
  rules:transducer_rule list
}

let null_symb = ("0",0)
let null_sig = ([null_symb]:signature)
let null_node = Node("0",[])
let null_tree = ((null_sig,null_node):ranked_tree)
let null_ctx = Ctx_node("0",[])
let null_trans = {sigin = null_sig ;
                 sigout = null_sig ; 
                 nbstates = 1 ; 
                 axiom = null_ctx ; 
                 rules = []}
let null_rule = (("0",1),null_ctx)
let bottom_ctx = Ctx_hole(-1,-1)

exception NoRule of string

(* Fonctions d'affichage *)

let print_symbol (symb,arity) =
  print_endline ("("^symb^","^(string_of_int arity)^")")

let rec print_ctx = function
  | Ctx_node(symb,ctx_list) -> 
    print_string symb;
    let rec print_ctx_list = function
      | [] -> ()
      | x::[] -> print_ctx x
      | x::xs -> print_ctx x;
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
    print_string ("q"^(string_of_int state)^"(x"^(string_of_int childnum)^")")
    
let print_DTOP_rule ((symb,state),ctx) = 
  print_string ("q"^(string_of_int state)^"("^symb^") -> ");
  print_ctx ctx;
  print_newline ()
  
let print_DTOP trans =
  print_endline "Signature d'entrée :";
  iter print_symbol trans.sigin;
  print_endline "Signature de sortie :";
  iter print_symbol trans.sigout;
  print_endline "Axiome :";
  print_ctx trans.axiom;
  print_newline ();
  print_endline "Règles :";
  iter print_DTOP_rule trans.rules

(* Fonctions de vérification *)

let rec check_sig = function
  | [] -> true
  | (symb,_)::tail -> not(mem_assoc symb tail) && (check_sig tail)

  
let rec check_tree ((signature,Node(name,children)):ranked_tree) =  
  fold_left 
    (fun a b -> a && (check_tree (signature,b)) ) 
    (mem (name,length children) signature) 
    children
  

let rec check_trans_rule sigin sigout nbstates symbin statein= function
  | Ctx_hole(stateout,chil) -> 
    statein > 0 && statein <= nbstates && stateout > 0 && stateout <= nbstates 
    && mem_assoc symbin sigin && chil > 0 && chil <= assoc symbin sigin
    
  | Ctx_node(symbout,children) -> 
    fold_left 
      (fun a b -> check_trans_rule sigin sigout nbstates symbin statein b && a) 
      (mem (symbout, length children) sigout) 
      children
    

let check_trans (trans:dtop_transducer) = 
  fold_left 
    (
      fun a b -> 
        let ((symb,state),context) = b in 
        a && (check_trans_rule trans.sigin trans.sigout trans.nbstates symb state context)
    ) 
    (check_trans_rule [("0",1)] trans.sigout trans.nbstates "0" 1 trans.axiom) 
    trans.rules
    
let rec compatible_signatures = function
  | ([],sig2) -> true
  | ((symb,arity)::tail,sig2) -> (mem (symb,arity) sig2) && compatible_signatures (tail,sig2)


(* Application d'un transducteur à un arbre *)

let rec ctx_to_tree = function
  | Ctx_node(symb,children) -> 
    Node(
      symb,
      fold_left (fun a b -> (ctx_to_tree b)::a) [] children
    )
  | Ctx_hole(state,childnum) -> failwith "Context contains calls"
    

let rec apply_rules rules = function 
  | (node,Ctx_node(symbout,children)) -> 
    Ctx_node(symbout, fold_left (fun a b -> (apply_rules rules (node,b))::a) [] children) 
    
  | (Node(symbin,childin),Ctx_hole(state,child_number)) ->
    let Node(symbin,childin) = nth childin (child_number-1) in 
      if not (mem_assoc (symbin,state) rules) then failwith "Input is out of domain" else
      apply_rules rules (Node(symbin,childin), assoc (symbin,state) rules)  
    

let apply (trans:dtop_transducer) (tree:ranked_tree) = 
  if not ((check_sig trans.sigin) && (check_sig trans.sigout) && check_trans trans) 
  then failwith "Ill-defined transducer" else
  if not ((check_sig (fst tree)) && check_tree tree) 
  then failwith "Ill-defined tree" else
  if not (compatible_signatures ((fst tree),trans.sigin)) 
  then failwith "Signatures are not compatible" else
  ((trans.sigout,ctx_to_tree (apply_rules trans.rules (Node("0",[(snd tree)]), trans.axiom))):ranked_tree)
  
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

