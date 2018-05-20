open List
open Utils
open DTOP_Transducers
open DTT_Automata
open IO_xml
open Operations
open Generators
open Timer

(*Définition des constantes de test par défaut*)

let core_number = ref 1

let nb_symb_min = ref 4
let nb_symb_max = ref 4
let nb_symb_step = ref 4

let max_arity_min = ref 4
let max_arity_max = ref 4
let max_arity_step = ref 4

let path_length_min = ref 4
let path_length_max = ref 4
let path_length_step = ref 4

(*Lecture du fichier de configuration*)

let parse_conf_file filename =
  let conf_file = open_in filename in
  let couples = ref [] in
  try 
    while true 
    do
      let line = input_line conf_file in
      let args = Str.split (Str.regexp " = ") line in
      couples := (nth args 0,nth args 1)::!couples
    done;
  with End_of_file ->
    close_in conf_file;
    
  let couples = !couples in
  
  if mem_assoc "core_number" couples
  then core_number := int_of_string (assoc "core_number" couples);  
  
  if mem_assoc "nb_symb_min" couples
  then nb_symb_min := int_of_string (assoc "nb_symb_min" couples);
  
  if mem_assoc "nb_symb_max" couples
  then nb_symb_max := int_of_string (assoc "nb_symb_max" couples);
  
  if mem_assoc "nb_symb_step" couples
  then nb_symb_step := int_of_string (assoc "nb_symb_step" couples);  
  
  if mem_assoc "max_arity_min" couples
  then max_arity_min := int_of_string (assoc "max_arity_min" couples);
  
  if mem_assoc "max_arity_max" couples
  then max_arity_max := int_of_string (assoc "max_arity_max" couples);
  
  if mem_assoc "max_arity_step" couples
  then max_arity_step := int_of_string (assoc "max_arity_step" couples);  
  
  if mem_assoc "path_length_min" couples
  then path_length_min := int_of_string (assoc "path_length_min" couples);
  
  if mem_assoc "path_length_max" couples
  then path_length_max := int_of_string (assoc "path_length_max" couples);
  
  if mem_assoc "path_length_step" couples
  then path_length_step := int_of_string (assoc "path_length_step" couples)
  

(*Définition fonctions de test*)

let test_comp_equiv nb_symb max_arity path_length =
  let time_0 = Unix.gettimeofday() in
  (*print_endline "======Génération=======";*)
  let ((a1,t1),(a2,t2)) = make_random_transducer_pair nb_symb max_arity path_length in
  let t_ID = make_ID_transducer a1.signature in
  let time_1 = Unix.gettimeofday() in
  (*print_endline "======Composition======";*)
  let (a_comp,t_comp) = compose_DI (a1,t1) (a2,t2) in
  let time_2 = Unix.gettimeofday() in
  (*print_endline "======Équivalence======";*)
  let _ = trans_equality (a_comp,t_comp) (a1,t_ID) in
  let time_3 = Unix.gettimeofday() in
  let time_tuple = (time_1-.time_0,time_2-.time_1,time_3-.time_2) in
  let size_tuple = (length t1.sigin,t1.nbstates, length t1.rules) in
  (size_tuple,time_tuple)
  
let memory_usage_test () = 
  iter
  (fun _ -> 
    print_endline "test";
    let _ = test_comp_equiv 5 5 150 in
    print_endline "attente";
    Unix.sleep 5
  )
  (range 10)
  
let output_results ()=
  let sofi = string_of_int in
  let filename = 
  "Results/results_"
  ^(sofi !nb_symb_max)
  ^"_"^(sofi !max_arity_max)
  ^"_"^(sofi !path_length_max)
  ^".txt" in
  let out_file = open_out filename in
  let single_output ((i,j,k),((n1,n2,n3),(f1,f2,f3))) =
    Printf.fprintf 
      out_file 
      "%d,%d,%d,%d,%d,%d,%f,%f,%f\n"
      i j k n1 n2 n3 f1 f2 f3;
    flush out_file
  in
  let tuples = 
    map 
    ( fun i ->
      map 
      ( fun j -> 
        map
        ( fun k -> (i,j,k))
        (range3 !path_length_min !path_length_max !path_length_step)
      )
      (range3 !max_arity_min !max_arity_max !max_arity_step)
    )
    (range3 !nb_symb_min !nb_symb_max !nb_symb_step)
  in
  let tuples = flatten (flatten tuples) in
  
  let dist_values = Array.make !core_number [] in
  
  let i = ref 0 in
  let deal_tuple tuple =
    dist_values.(!i) <- tuple::(dist_values.(!i));
    i := ((!i+1) mod !core_number)
  in
    
  iter deal_tuple (rev tuples);  
  let temp_tuples = ref (Array.to_list dist_values) 
  and own_tuples = ref [] in
  
  (* Début multiprocessing *)
  
  let pid = ref (Unix.getpid ())
  and children = ref [] in
  
  while (((length !children) < !core_number) && (!pid <> 0))
  do
    pid := (Unix.fork());
    children := !pid::!children;
    own_tuples := hd (!temp_tuples);
    temp_tuples := tl (!temp_tuples)
  done;
  
  if (!pid = 0)
  
  then begin (*Processus enfants*)
    iter 
    (fun (i,j,k) ->
      print_endline 
        ((sofi (Unix.getpid()))^" Testing ("^(sofi i)^","^(sofi j)^","^(sofi k)^")");
      let res = test_comp_equiv i j k in
      single_output ((i,j,k),res);
      Gc.full_major ()
    )
    !own_tuples;
    
    Printf.printf 
      "Timers %d : %f,%f,%f,%f,%f,%f,%f,%f,%f,%f\n%f,%f,%f\n"
      (Unix.getpid())
      !timer0
      !timer1
      !timer2
      !timer3
      !timer4
      !timer5
      !timer6
      !timer7
      !timer8
      !timer9
      !timerA
      !timerB
      !timerC;
  end 
  
  else begin (*Processus parent*)
    let _ = map (fun childpid -> Unix.waitpid [] childpid) !children in
    close_out out_file;
    print_endline "Shutting down"
  end;
  
