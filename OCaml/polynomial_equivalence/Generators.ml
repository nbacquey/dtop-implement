open List
open Utils
open DTOP
open Default_Structures

module Gen_DTOP = DTOP (Tree_Signature) (Tree_Signature) (Int_State)
module Tree = Ranked_Tree (Tree_Signature)
module Context = Ranked_Context (Tree_Signature) (Int_State)

module IntSet = Gen_DTOP.State_set
  
open Gen_DTOP
open Tree
open Context

(*Construction transducteur identité*)
let make_ID_rule symb arity = 
  ((symb,1),Context.Ctx_node(symb, Array.to_list (Array.init arity (fun a -> Context.Ctx_hole(1,a+1)) ) ))

let make_ID_transducer signature = 
  
  let states = IntSet.empty in
  {
    sigin = signature;
    sigout = signature;
    states = IntSet.add 1 states;
    axiom = Context.Ctx_hole(1,1);
    rules = fold_left
      (fun a (symb,arity) -> (make_ID_rule symb arity)::a)
      []
      signature
  }
  
(*Construction d'une signature*)

let make_sig nb_symb max_arity = 

  let make_symb (n,arity) = ("S"^(string_of_int n)^"_"^(string_of_int arity),arity) in
  
  let pairs = flatten (
    map 
    ( fun i ->
      map 
      ( fun j -> (i,j-1) )
      (range (max_arity+1))
    )
    (range nb_symb)
  ) in    
  
  map make_symb pairs


(*Décomposition d'un path "naturel" en paires d'entiers*)
let decompose_path path =
  
  if path = "/" then [] else
  let reg = Str.regexp "^\\(/[0-9]+_[0-9]+\\)+$" in
  if not (Str.string_match reg path 0)
  then failwith "Path does not match regexp"
  else
    let path_split = Str.split (Str.regexp "/") path in
    
    map
    (fun str ->
      let int_vals = Str.split (Str.regexp "_") str in
      (int_of_string (hd int_vals), int_of_string (nth int_vals 1))
    )
    path_split
    
let arity_compatible path max_arity = fold_left
  (fun a (_,childnum) -> a && (childnum <= max_arity)) true path
  
(*Construction d'un transducteur d'installation *)
let make_trans_install nb_symb max_arity path =

  let sigin = make_sig nb_symb max_arity in
  let sigout = ("PKG",0)::sigin in
  let rules = ref [] in  
  
  let path_pairs = decompose_path path in
  if not(arity_compatible path_pairs max_arity) 
  then failwith "Max arity is not compatible with given path"
  else
  
  let state_set = fold_right (IntSet.add) (range ((length path_pairs)+2)) IntSet.empty in
  
  let state_ID = (length path_pairs)+2 in
  let state_num = ref 1 in
  
  let path_pair_to_rules (symb_num, child_num) =
    let arity = ref child_num in
    while (!arity <= max_arity)
    do
      let symb = "S"^(string_of_int symb_num)^"_"^(string_of_int !arity) in
      let calls_array = Array.init 
        !arity 
        (fun x -> if (x <> child_num -1) then Ctx_hole(state_ID,x+1) else Ctx_hole(!state_num+1,x+1)) 
      in
      
      let rule = ((symb,!state_num),Ctx_node(symb, Array.to_list calls_array)) in
      rules := rule::!rules;
      incr arity
    done;
    incr state_num
  in
  
  iter path_pair_to_rules path_pairs;
  
  let make_pkg_rules arity = 
    let make_pkg_rule symb_num =
      let symb_base = "S"^(string_of_int symb_num)^"_" in
      let calls_array = Array.init (arity-1) (fun n -> Ctx_hole(state_ID,n+1)) in
      let ctx_list = (Array.to_list calls_array)@[Ctx_node("PKG",[])] in
      
      let symb_before = symb_base^(string_of_int (arity-1))
      and symb_after = symb_base^(string_of_int arity) in
      
      let rule = ((symb_before,!state_num),Ctx_node(symb_after,ctx_list)) in
      rules := rule::!rules
    in
    
    iter make_pkg_rule (range nb_symb)
  in
  
  iter make_pkg_rules (range max_arity);
  
  let make_ID_rule (symb_num,arity) =
    let ctx_list = Array.to_list (Array.init arity (fun n -> Ctx_hole(state_ID,n+1))) in
    let symb = "S"^(string_of_int symb_num)^"_"^(string_of_int arity) in
    let rule = ((symb,state_ID),Ctx_node(symb,ctx_list)) in
    rules := rule::!rules
  in
  
  let pairs = flatten (
    map 
    ( fun i ->
      map 
      ( fun j -> (i,j-1) )
      (range (max_arity+1))
    )
    (range nb_symb)
  ) in
  
  iter make_ID_rule pairs;
  
  {
    sigin;
    sigout;
    states = state_set;
    axiom = Ctx_hole(1,1);
    rules = !rules
  }
  
(*Construction d'un transducteur de désinstallation *)
let make_trans_uninstall nb_symb max_arity path =

  let sigout = make_sig nb_symb max_arity in
  let sigin = ("PKG",0)::sigout in
  let rules = ref [] in
  
  let path_pairs = decompose_path path in
  if not(arity_compatible path_pairs max_arity) 
  then failwith "Max arity is not compatible with given path"
  else 
  
  let state_set = fold_right (IntSet.add) (range ((length path_pairs)+2)) (IntSet.empty) in
  
  let state_ID = (length path_pairs)+2 in
  let state_num = ref 1 in
  
  let path_pair_to_rules (symb_num, child_num) =
    let arity = ref child_num in
    while (!arity <= max_arity)
    do
      let symb = "S"^(string_of_int symb_num)^"_"^(string_of_int !arity) in
      let calls_array = Array.init 
        !arity 
        (fun x -> if (x <> child_num -1) then Ctx_hole(state_ID,x+1) else Ctx_hole(!state_num+1,x+1)) 
      in
      
      let rule = ((symb,!state_num),Ctx_node(symb, Array.to_list calls_array)) in
      rules := rule::!rules;
      incr arity
    done;
    incr state_num
  in
  
  iter path_pair_to_rules path_pairs;
  
  let make_pkg_rules arity = 
    let make_pkg_rule symb_num =
      let symb_base = "S"^(string_of_int symb_num)^"_" in
      let calls_array = Array.init (arity-1) (fun n -> Ctx_hole(state_ID,n+1)) in
      let ctx_list = (Array.to_list calls_array) in
      
      let symb_before = symb_base^(string_of_int arity)
      and symb_after = symb_base^(string_of_int (arity-1)) in
      
      let rule = ((symb_before,!state_num),Ctx_node(symb_after,ctx_list)) in
      rules := rule::!rules
    in
    
    iter make_pkg_rule (range nb_symb)
  in
  
  iter make_pkg_rules (range max_arity);
  
  let make_ID_rule (symb_num,arity) =
    let ctx_list = Array.to_list (Array.init arity (fun n -> Ctx_hole(state_ID,n+1))) in
    let symb = "S"^(string_of_int symb_num)^"_"^(string_of_int arity) in
    let rule = ((symb,state_ID),Ctx_node(symb,ctx_list)) in
    rules := rule::!rules
  in
  
  let pairs = flatten (
    map 
    ( fun i ->
      map 
      ( fun j -> (i,j-1) )
      (range (max_arity+1))
    )
    (range nb_symb)
  ) in
  
  iter make_ID_rule pairs;
  
  {
    sigin;
    sigout;
    states = state_set;
    axiom = Ctx_hole(1,1);
    rules = !rules
  }
  
(*Génération de paires de transducteurs install/uninstall aléatoires*)

let _ = Random.self_init ()

let make_random_path nb_symb max_arity path_length=
  
  let pairs_array = Array.init path_length (fun _ -> ((Random.int nb_symb)+1,(Random.int max_arity)+1)) in
  fold_left
    (fun path (symb_num,child_num) ->
      "/"^(string_of_int symb_num)^"_"^(string_of_int child_num)^path
    )
    ""
    (Array.to_list pairs_array)

let make_random_transducer_pair nb_symb max_arity path_length =
  let path = make_random_path nb_symb max_arity path_length in
  
  let trans_ins = make_trans_install nb_symb max_arity path
  and trans_des = make_trans_uninstall nb_symb max_arity path in
 
  (trans_ins,trans_des)
  
(* Génération de paires de transducteurs équivalents non triviaux *)

let make_kary_signature prefix nb_symb arity = 
  let pre_sig = map 
  (fun n -> (prefix^"_"^(string_of_int n),arity))
  (range nb_symb) in
  
  (prefix^"_#1",0)::((prefix^"_#2",0))::pre_sig

(*Méthode 1 : double demi-mot*)

let make_early_rules_1 word_size = 
  let init_rules = [
    (("S_1",1),Ctx_node("S_1",[Ctx_hole(2,1);Ctx_hole(2,1)]));
    (("S_2",1),Ctx_node("S_2",[Ctx_hole(word_size+2,1);Ctx_hole(word_size+2,1)]));
    (("S_#1",word_size+1),Ctx_node("S_#1",[]));
    (("S_#2",word_size+1),Ctx_node("S_#2",[]));
    (("S_#1",2*word_size+1),Ctx_node("S_#1",[]));
    (("S_#2",2*word_size+1),Ctx_node("S_#2",[]))
  ] in
  
  let producing_rules = fold_left 
  (fun rule_list n -> 
    (("S_1",n),Ctx_node("S_1",[Ctx_hole(n+1,1);Ctx_hole(n+1,1)]))::
    (("S_2",n+word_size),Ctx_node("S_2",[Ctx_hole(n+word_size+1,1);Ctx_hole(n+word_size+1,1)]))::rule_list 
  )
  []
  (range3 2 (word_size/2) 1) in
  
  let consuming_rules = fold_left 
  (fun rule_list n -> 
    (("S_1",n),Ctx_hole(n+1,1))::
    (("S_2",n+word_size),Ctx_hole(n+word_size+1,1))::rule_list 
  )
  []
  (range3 (word_size/2+1) word_size 1) in
  
  init_rules@consuming_rules@producing_rules
  
  
let make_late_rules_1 word_size = 
  let init_rules = [
    (("S_1",1),Ctx_hole(2,1));
    (("S_2",1),Ctx_hole(word_size+2,1));
    (("S_#1",word_size+1),Ctx_node("S_#1",[]));
    (("S_#2",word_size+1),Ctx_node("S_#2",[]));
    (("S_#1",2*word_size+1),Ctx_node("S_#1",[]));
    (("S_#2",2*word_size+1),Ctx_node("S_#2",[]))
  ] in
  
  let consuming_rules = fold_left 
  (fun rule_list n -> 
    (("S_1",n),Ctx_hole(n+1,1))::
    (("S_2",n+word_size),Ctx_hole(n+word_size+1,1))::rule_list 
  )
  []
  (range3 2 (word_size/2) 1) in
  
  let producing_rules = fold_left 
  (fun rule_list n -> 
    (("S_1",n),Ctx_node("S_1",[Ctx_hole(n+1,1);Ctx_hole(n+1,1)]))::
    (("S_2",n+word_size),Ctx_node("S_2",[Ctx_hole(n+word_size+1,1);Ctx_hole(n+word_size+1,1)]))::rule_list
  )
  []
  (range3 (word_size/2+1) word_size 1) in
  
  init_rules@consuming_rules@producing_rules

let make_twin_transducers_1 unary_word_size = 
  let input_signature = make_kary_signature "S" 2 1 
  and output_signature = make_kary_signature "S" 2 2 
  and state_set = IntSet.of_list (range (2*unary_word_size+1)) in
  
  let dtop_late = {
    sigin = input_signature;
    sigout = output_signature;
    states = state_set;
    axiom = Ctx_hole(1,1);
    rules = make_late_rules_1 unary_word_size
  } in 
  
  let dtop_early = {
    sigin = input_signature;
    sigout = output_signature;
    states = state_set;
    axiom = Ctx_hole(1,1);
    rules = make_early_rules_1 unary_word_size
  } in 
  
  (dtop_early,dtop_late)
  
(*Méthode 2 : test équivalence i/j *)

let make_early_rules_2 block_size pos_i pos_j =
  let fixed_rules = [
    (("T_#1",1),Ctx_node("T_#1",[]));
    (("T_#2",1),Ctx_node("T_#2",[]));
    (("T_1",pos_i),Ctx_node("T_1",[Ctx_hole(pos_i+1,1);Ctx_hole(pos_i+1,1)]));
    (("T_2",pos_i),Ctx_node("T_2",[Ctx_hole(pos_j+1,1);Ctx_hole(pos_j+1,1)]));
    (("T_1",pos_j),Ctx_hole(2*pos_j-pos_i+1,1));
    (("T_2",2*pos_j-pos_i),Ctx_hole(2*pos_j-pos_i+1,1));
    (("T_1",block_size+pos_j-pos_i),Ctx_hole(1,1));
    (("T_2",block_size+pos_j-pos_i),Ctx_hole(1,1))
  ] in
  
  let before_rules = fold_left 
  (fun rule_list n -> 
    (("S_1",n),Ctx_hole(n+1,1))::
    (("S_2",n),Ctx_hole(n+1,1))::rule_list
  )
  []
  (range (pos_i-1)) in
  
  let after_rules = fold_left 
  (fun rule_list n -> 
    (("S_1",n),Ctx_hole(n+1,1))::
    (("S_2",n),Ctx_hole(n+1,1))::rule_list
  )
  []
  (range3 (2*pos_j-pos_i+1) (block_size+pos_j-pos_i-1) 1) in
  
  let between_rules = fold_left
  (fun rule_list n ->
    (("S_1",n),Ctx_hole(n+1,1))::
    (("S_2",n),Ctx_hole(n+1,1))::
    (("S_1",n+pos_j-pos_i),Ctx_hole(n+pos_j-pos_i+1,1))::
    (("S_2",n+pos_j-pos_i),Ctx_hole(n+pos_j-pos_i+1,1))::rule_list
  )
  []
  (range3 (pos_i+1) (pos_j-1) 1) in
  
  fixed_rules@before_rules@between_rules@after_rules
  

let make_late_rules_2 block_size pos_i pos_j =
  let fixed_rules = [
    (("T_#1",1),Ctx_node("T_#1",[]));
    (("T_#2",1),Ctx_node("T_#2",[]));
    (("T_1",pos_i),Ctx_hole(pos_i+1,1));
    (("T_2",pos_i),Ctx_hole(pos_j+1,1));
    (("T_1",pos_j),Ctx_node("T_1",[Ctx_hole(2*pos_j-pos_i+1,1);Ctx_hole(2*pos_j-pos_i+1,1)]));
    (("T_2",2*pos_j-pos_i),Ctx_node("T_2",[Ctx_hole(2*pos_j-pos_i+1,1);Ctx_hole(2*pos_j-pos_i+1,1)]));
    (("T_1",block_size+pos_j-pos_i),Ctx_hole(1,1));
    (("T_2",block_size+pos_j-pos_i),Ctx_hole(1,1))
  ] in
  
  let before_rules = fold_left 
  (fun rule_list n -> 
    (("S_1",n),Ctx_hole(n+1,1))::
    (("S_2",n),Ctx_hole(n+1,1))::rule_list
  )
  []
  (range (pos_i-1)) in
  
  let after_rules = fold_left 
  (fun rule_list n -> 
    (("S_1",n),Ctx_hole(n+1,1))::
    (("S_2",n),Ctx_hole(n+1,1))::rule_list
  )
  []
  (range3 (2*pos_j-pos_i+1) (block_size+pos_j-pos_i-1) 1) in
  
  let between_rules = fold_left
  (fun rule_list n ->
    (("S_1",n),Ctx_hole(n+1,1))::
    (("S_2",n),Ctx_hole(n+1,1))::
    (("S_1",n+pos_j-pos_i),Ctx_hole(n+pos_j-pos_i+1,1))::
    (("S_2",n+pos_j-pos_i),Ctx_hole(n+pos_j-pos_i+1,1))::rule_list
  )
  []
  (range3 (pos_i+1) (pos_j-1) 1) in
  
  fixed_rules@before_rules@between_rules@after_rules

(*We must have 1 < i < j < block_size*)
let make_twin_transducers_2 block_size pos_i pos_j = 
  let input_signature = make_kary_signature "T" 2 1 
  and output_signature = make_kary_signature "T" 2 2 
  and state_set = IntSet.of_list (range (block_size + pos_j - pos_i)) in
  
  let dtop_late = {
    sigin = input_signature;
    sigout = output_signature;
    states = state_set;
    axiom = Ctx_hole(1,1);
    rules = make_late_rules_2 block_size pos_i pos_j
  } in 
  
  let dtop_early = {
    sigin = input_signature;
    sigout = output_signature;
    states = state_set;
    axiom = Ctx_hole(1,1);
    rules = make_early_rules_2 block_size pos_i pos_j
  } in 
  
  (dtop_early,dtop_late)

(*Méthode 3 : transducteurs identité non triviaux*)
type node = Term of int list | Node of node * node

let make_nontrivial_identity_rules block_height redundant_states =
  let n = block_height 
  and k = redundant_states in
  let state_number = (pow 2 (block_height))-1 in

  let rec make_block path = function 
    | 0 -> Term(path)
    | n -> Node(make_block (path@[0]) (n-1),make_block (path@[1]) (n-1)) in
  
  let compute_state path =
    let base = pow 2 (length path) in
    
    let (shift,_) = fold_left 
    (fun (acc,pow_2) bit -> (acc+bit*pow_2,2*pow_2))
    (0,1)
    path in    
    
    (shift+base)+state_number*(Random.int k) in
    
  let compute_state_range path = 
    let base = pow 2 (length path) in
    
    let (shift,_) = fold_left 
    (fun (acc,pow_2) bit -> (acc+bit*pow_2,2*pow_2))
    (0,1)
    path in    
    
    range3 (shift+base) (shift+base+(k-1)*state_number) state_number in

  let base_block = make_block [] n in
    
  let rec randomize_block = function
    | Term(hd::path) -> Ctx_hole(compute_state path,hd+1)
    | Node(node_1,node_2) -> Ctx_node("U_1",[(randomize_block node_1);(randomize_block node_2)]) 
    | _ -> failwith "badly defined block" in
    
  let initial_rules = 
    (map 
    (fun q -> (("U_#1",q),Ctx_node("U_#1",[])))
    (compute_state_range [])) @
    (map 
    (fun q -> (("U_#2",q),Ctx_node("U_#2",[])))
    (compute_state_range [])) @
    (map 
    (fun q -> (("U_1",q),randomize_block base_block))
    (compute_state_range [])) in
    
  let rec generate_paths = function 
    | 0 -> [[]]
    | n -> let shorter_paths = generate_paths (n-1) in
      (map (fun path -> 0::path) shorter_paths) @
      (map (fun path -> 1::path) shorter_paths) in
      
  let paths = fold_left
    (@)
    []
    (map (generate_paths) (range (n-1))) in
    
  let path_to_rules path = match path with
    | hd::tl ->
      map 
        (fun q -> (("U_1",q),Ctx_hole(compute_state tl,hd+1) ))
        (compute_state_range path) 
    | [] -> failwith "can't automatically define rules for empty path" in
    
  let consuming_rules = fold_left
  (@)
  []
  (map path_to_rules paths) in
  
  initial_rules @ consuming_rules
    

let make_nontrivial_identity_transducer block_height redundant_states =
  let signature = make_kary_signature "U" 1 2 
  and state_set = IntSet.of_list (range ((pow 2 (block_height-1))*redundant_states)) in
  {
    sigin = signature;
    sigout = signature;
    states = state_set;
    axiom = Ctx_hole(1,1);
    rules = make_nontrivial_identity_rules block_height redundant_states
  }
