open List

(* Fonctions utilitaires *)
let range n = 
  let rec inv_range = function
    | 0 -> []
    | k -> k::(inv_range (k-1))
  in rev (inv_range n)
  
let range3 min_val max_val step =
  let cur = ref min_val in
  let res = ref [] in
  while !cur <= max_val 
  do
    res := !cur::!res;
    cur := !cur+step
  done;
  rev !res
 
let rec remove e = function 
  | [] -> []
  | x::xs -> if x=e then (remove e xs) else x::(remove e xs)

let rec nub = function
  | [] -> []
  | x::xs -> x::(nub (remove x xs))
 
let rec intersect_sorted l1 l2 =
  match l1 with
    | [] -> []
    | h1::t1 -> (
      match l2 with 
        [] -> []
        | h2::t2 when h1 < h2 -> intersect_sorted t1 l2
        | h2::t2 when h1 > h2 -> intersect_sorted l1 t2
        | h2::t2 -> h1::(intersect_sorted t1 t2)
    )
    
let intersect comparator l1 l2 = 
  let l1 = sort comparator l1
  and l2 = sort comparator l2
  in intersect_sorted l1 l2
  
class ['a] agenda = object
  val  todo_list : ('a list ref) = ref []
  val  done_list : ('a list ref) = ref []
  
  method is_empty () = 
    (!todo_list = [])
  
  method add (task : 'a) = 
    if not((mem task !todo_list) || (mem task !done_list))
    then todo_list := task::(!todo_list)
    
  method retrieve () = match !todo_list with
    | [] -> failwith "Nothing more to do"
    | x::xs -> x
    
  method deliver (task : 'a) = 
    if not(mem task !done_list)
    then done_list := task::(!done_list) ; 
    todo_list := (remove task !todo_list)    
  
end

class ['a] indexator = object
  val  contents : (('a * int) list ref) = ref []
  
  method get_index_of obj =
    if (mem_assoc obj !contents)
    then assoc obj !contents
    else ( 
      contents := ((obj,(length !contents)+1)::!contents);
      length !contents)
      
  method get_records_count () =
    length !contents
      
end

