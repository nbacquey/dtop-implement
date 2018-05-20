open List
open Utils
open DTOP_Transducers
open DTT_Automata
open IO_xml

(*Construction transducteur identité*)
let make_ID_rule symb arity = 
  ((symb,1),Ctx_node(symb, Array.to_list (Array.init arity (fun a -> Ctx_hole(1,a+1)) ) ))

let make_ID_transducer signature = 
  {
    sigin = signature;
    sigout = signature;
    nbstates = 1;
    axiom = Ctx_hole(1,1);
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
    nbstates = !state_num+1;
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
    nbstates = !state_num+1;
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
  
  let aut_ins = make_DI_automaton trans_ins
  and aut_des = make_DI_automaton trans_des in
  
  ((aut_ins,trans_ins),(aut_des,trans_des))
