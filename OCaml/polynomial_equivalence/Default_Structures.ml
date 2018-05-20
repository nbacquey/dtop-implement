open List
open Signatures


module Int_State =
struct 
  type t = int 
  let default_state = -1
  let printable_value = string_of_int
  let compare = compare
end

module Couple_State =
functor (State1 : Formal_State_Sig) ->
functor (State2 : Formal_State_Sig) ->
struct 
  type t = State1.t * State2.t 
  let default_state = (State1.default_state,State2.default_state)
  let printable_value (n1,n2) = "("^(State1.printable_value n1)^","^(State2.printable_value n2)^")"
  let compare (n11,n12) (n21,n22) = 
    let c = State1.compare n11 n21 in 
    if (c != 0) then c else State2.compare n12 n22
end

module Tree_Signature =
struct
  type label = string
  type signature = (label * int) list
  let default_label = "None"
  let default_signature = [(default_label,0)]
  
  let rec check_sig = function
    | [] -> true
    | (symb,_)::tail -> not(mem_assoc symb tail) && (check_sig tail)
    
  let print = 
    iter (fun (label,arity) -> print_endline ("("^label^","^(string_of_int arity)^")"))
    
  let printable_value label = label
  let compare = String.compare
end

module Ranked_Tree = 
functor (Sig : Ranked_Signature_Sig) -> 
struct
  
  type label = Sig.label
  type ranked_tree = Node of (label * ranked_tree list)
  
  let default_tree = 
    let l = Sig.default_label in
    Node(l,[])
    
  let rec check_tree (signature,Node(name,children)) =  
  fold_left 
    (fun a b -> a && (check_tree (signature,b)) ) 
    (mem (name,length children) signature) 
    children
    
  let rec print (Node(label,tree_list)) = 
    print_string (Sig.printable_value label);
    let rec print_list = function
      | [] -> ()
      | x::[] -> print x
      | x::xs -> print x;
        print_string ",";
        print_list xs
    in
    
    if (length tree_list) > 0
    then begin
      print_string "(";
      print_list tree_list;
      print_string ")"
    end
    
    
end

module Ranked_Context =
functor (Sig : Ranked_Signature_Sig) ->
functor (States : Formal_State_Sig) -> 
struct 

  type label = Sig.label
  type state = States.t
  
  type ranked_context = Ctx_hole of (state * int) | Ctx_node of (label * ranked_context list)
  
  let default_context = 
    let l = Sig.default_label in
    Ctx_node(l,[])
    
  let rec is_constant = function
    | Ctx_hole(_,_) -> false
    | Ctx_node(_,ctx_list) -> fold_left
      (fun acc ctx -> acc && (is_constant ctx))
      true
      ctx_list
    
  let rec print = function
  | Ctx_node(label,ctx_list) -> 
    print_string (Sig.printable_value label);
    let rec print_ctx_list = function
      | [] -> ()
      | x::[] -> print x
      | x::xs -> print x;
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
    print_string ("q"^(States.printable_value state)^"(x"^(string_of_int childnum)^")")
    
(* Factorisation Arbre vers DAG *)
    
  let rec (===) ctx1 ctx2 = 
    if ctx1 == ctx2 then true else match (ctx1,ctx2) with
    | (Ctx_hole(a1,b1),Ctx_hole(a2,b2)) -> (a1 = a2) && (b1 = b2)
    | (Ctx_node(symb1, ctx_list1),Ctx_node(symb2, ctx_list2)) ->
      if symb1 <> symb2 then false else
      fold_left2
      (fun acc ctx1 ctx2 ->
        acc && (ctx1 === ctx2)
      )
      true
      ctx_list1
      ctx_list2
    | _ -> false
  
  let rec factorize_context = function
    | Ctx_hole(state,child) -> Ctx_hole(state,child)
    | Ctx_node(symb,ctx_list) -> 
      let rec indexate i = function
        | [] -> []
        | x::xs -> (x,i)::(indexate (i+1) xs) in
        
      let indexed_list = indexate 0 ctx_list in
      
      let rec tag_element (x,i) k = function
        | [] -> []
        | (y,j)::tl -> 
          if (j < k) || (not (x === y))
          then
            (y,j)::(tag_element (x,i) (k+1) tl)
          else
            (y,i)::(tag_element (x,i) (k+1) tl) in
            
      let rec tag_all k = function
        | [] -> []
        | (x,i)::tail -> (x,i)::(tag_all (k+1) (tag_element (x,i) k tail)) in
        
      let tagged_list = tag_all 0 indexed_list in
      
      let rec replace (new_x,i) = function 
        | [] -> []
        | (x,j)::tail -> if i = j 
          then (new_x,-1)::(replace (new_x,i) tail)
          else (x,j)::(replace (new_x,i) tail) in
          
      let rec replace_all = function 
        | [] -> []
        | (x,i)::tail -> if i = -1
          then (x,i)::(replace_all tail)
          else 
            let new_x = factorize_context x in
            (new_x,-1)::(replace_all (replace (new_x,i) tail)) in
            
      let replaced_list = replace_all tagged_list in
      
      Ctx_node(symb, map (fun (ctx,_) -> ctx) replaced_list)
    
(* Fonctions récursives intelligentes multi-usages de parcours de DAG *)

let rec mem_struct ctx = function
  | [] -> false
  | hd::tl -> (ctx == hd) || (mem_struct ctx tl)

let fold_dag f_node f_acc node = 
  let rec fold_visited visited node = 
    if mem_struct node visited then None else 
      let visited = node::visited in
      match node with
        | Ctx_hole(_,_) -> Some (f_node node,visited)
        | Ctx_node(s,ctx_list) -> fold_left 
          (fun opt ctx -> match opt with
              | Some (acc,visited) ->
                (let ret = fold_visited visited ctx in
                  match ret with
                    | None -> opt
                    | Some (new_acc,new_visited) -> Some (f_acc acc new_acc,new_visited)
                )
              | None -> failwith "No node visited, should not happen"
          ) 
          (Some (f_node node,visited))
          ctx_list in
          
  let ret = fold_visited [] node in
  match ret with
    | Some (x,_) -> x
    | None -> failwith "No node visited, should not happen"
    
    
let fold_dag2 f_node f_acc node1 node2 =
  let rec fold_visited visited1 visited2 node1 node2 = 
    if (mem_struct node1 visited1) && (mem_struct node2 visited2) then None
    else
      let (visited1,visited2) = (node1::visited1,node2::visited2) in
      match (node1,node2) with        
        | (Ctx_node(_,ctx_list1),Ctx_node(_,ctx_list2)) ->
          let base = (Some (f_node node1 node2,visited1,visited2)) in
          if (length ctx_list1) <> (length ctx_list2) then base else
          fold_left2
            (fun opt ctx1 ctx2 -> match opt with
              | Some (acc,visited1,visited2) ->
                (let ret = fold_visited visited1 visited2 ctx1 ctx2 in
                  match ret with
                    | None -> opt
                    | Some (new_acc,new_visited1,new_visited2) -> Some (f_acc acc new_acc,new_visited1,new_visited2)
                )
              | None -> failwith "No node visited, should not happen"
            ) 
            base
            ctx_list1
            ctx_list2
        | _ -> Some (f_node node1 node2,visited1,visited2) in
          
  let ret = fold_visited [] [] node1 node2 in
  match ret with
    | Some (x,_,_) -> x
    | None -> failwith "No node visited, should not happen"

let map_dag_leaves f_node node = 
  let rec map_visited visited node = 
    if mem_struct node !visited then node 
    else 
      match node with
        | Ctx_hole(_,_) -> 
          let node = f_node node in
          visited := node::!visited;
          node
        | Ctx_node(s,ctx_list) -> 
          let new_ctx_list = map (map_visited visited) ctx_list in
          let node = Ctx_node(s,new_ctx_list) in
          visited := node::!visited;
          node
  in
          
  map_visited (ref []) node 
    
end
