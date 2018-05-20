open Utils
open Signatures
open DTTA
open DTOP
open Generators
open Operations
open Equivalence
open Default_Structures

(* Quelques tests et exemples *)

module ExEquivalence = Equivalence (Tree_Signature) (Tree_Signature) (Int_State)
open ExEquivalence.Operations.Context_Before
open ExEquivalence.Operations.DTOP_Before

let print_before = ExEquivalence.Operations.DTOP_Before.print_DTOP
let print_after = ExEquivalence.Operations.DTOP_Product.print_DTOP

(* Transducteur non domain-wise *)

let signature = [
  ("f",3);
  ("A",0);
  ("B",0);
  ("C",0)
]

let states = Int_Set.of_list [0;1;2;3]

let axiom = Ctx_hole(0,1)

let rules = [
  (("f",0),Ctx_node("f",[Ctx_hole(1,1);Ctx_hole(2,1);Ctx_hole(3,3)]));
  (("A",1),Ctx_node("A",[]));
  (("B",1),Ctx_node("B",[]));
  (("B",2),Ctx_node("B",[]));
  (("C",2),Ctx_node("C",[]));
  (("B",3),Ctx_node("B",[]))
]

let dtop_unwise = {
  sigin = signature;
  sigout = signature;
  states;
  axiom;
  rules
}

(* Calcul du domaine, puis produit avec le transducteur *)

let dtop_wise = ExEquivalence.make_domain_wise dtop_unwise

(* Suppression des constantes *)

let dtop_noconst = ExEquivalence.remove_constants dtop_wise


(* Test de factorisation de contexte (Arbre -> DAG), les différences peuvent être testées avec fold_dag *)

let rec make_large_context = function
  | 0 -> Ctx_hole(0,1)
  | n -> Ctx_node("F",[make_large_context (n-1) ; make_large_context (n-1)])

let c1 = make_large_context 10

let c2 = factorize_context c1

(* Test de fold_dag2 et map_dag_leaves *)

let matches = fold_dag2
  (fun n1 n2 -> match (n1,n2) with
    | (Ctx_node(s1,_), Ctx_node(s2,_)) -> if s1 = s2 then 1 else 0
    | _ -> 0
  )
  (+)
  c1
  c2
  
let c3 = map_dag_leaves
  (fun ctx -> match ctx with
    | Ctx_node(_,_) -> ctx
    | Ctx_hole(_,_) -> Ctx_node("Answer",[Ctx_hole(42,42)])
  )
  c2
  
(* Tests de l'algorithme d'unification *)

open ExEquivalence.Operations.Context_Couple
let print_ctx = ExEquivalence.Operations.Context_Couple.print
let print_constraints = List.iter ExEquivalence.Unification_Constraint.print

let q1 = (1,1)
let q2 = (2,1)
let q3 = (3,1)
let q4 = (4,2)
let q5 = (5,2)

let ctx1 = 
  Ctx_node("F",
    [
      Ctx_hole(q1,1);
      Ctx_node("G",
        [
          Ctx_hole(q2,1);
          Ctx_node("H",[])
        ]
      )
    ]
  )
  
let ctx2 = 
  Ctx_node("F",
    [
      Ctx_node("G",
        [
          Ctx_hole(q2,2);
          Ctx_node("H",[])
        ]
      );
      Ctx_hole(q1,1)
    ]
  )
  
let ctx3 = 
  Ctx_node("F",
    [
      Ctx_hole(q1,1);
      Ctx_node("G",
        [
          Ctx_node("H",[]);
          Ctx_hole(q2,2)
        ]
      )
    ]
  )
  
let ctx4 =
  Ctx_hole(q3,1)
  
let ctx5 =
  Ctx_hole(q4,1)
  
let ctx6 =
  Ctx_hole(q5,1)
  
let l1 = ExEquivalence.context_unification ctx1 ctx2
let l2 = ExEquivalence.context_unification ctx1 ctx3
let l3 = ExEquivalence.context_unification ctx1 ctx4
let l4 = ExEquivalence.context_unification ctx1 ctx5
let l5 = ExEquivalence.context_unification ctx5 ctx6


(*
let s1 = ("f",2)
let s2 = ("g",2)
let s3 = ("a",1)
let s4 = ("b",1)
let s5 = ("c",1)
let s6 = ("#",0)

let (signature:signature) = [s1;s3;s6] 

let root1 =  Node("f", [
              Node("#",[]) ; 
              Node("f", [
                Node("#",[]) ; 
                Node("a",[
                  Node("a",[
                    Node("#",[])
                  ])
                ])
              ])
            ])
            
let root2 =  Node("g", [
              Node("#",[]) ; 
              Node("f", [
                Node("#",[]) ; 
                Node("a",[
                  Node("a",[
                    Node("#",[])
                  ])
                ])
              ])
            ])
            
let root3 =  Node("f", [
              Node("#",[]) ; 
              Node("f", [
                Node("#",[]) ; 
                Node("a",[
                  Node("a",[
                    Node("a",[])
                  ])
                ])
              ])
            ])
            
let root_ex =  Node("f", [
                Node("a", [
                  Node("b", [
                    Node("#", [])
                  ])
                ]) ;
                Node("a", [
                  Node("f", [
                    Node("#", []);
                    Node("b", [
                      Node("b", [
                        Node("a", [
                          Node("#", [])
                        ])
                      ])
                    ])
                  ])
                ])
              ])
            



let (sig1:signature) = [s1;s3;s4;s6]
let (sig2:signature) = [s2;s4;s5;s6]

let ax = Ctx_hole(1,1)

let rule1 = (("f",1),Ctx_node("g",[Ctx_hole(1,2) ; Ctx_hole(1,1)]))
let rule2 = (("a",1),Ctx_node("c",[Ctx_hole(1,1)]))
let rule3 = (("b",1),Ctx_node("b",[Ctx_hole(1,1)]))
let rule4 = (("#",1),Ctx_node("#",[]))

let rule1_ID = (("f",1),Ctx_node("f",[Ctx_hole(1,1) ; Ctx_hole(1,2)]))
let rule2_ID = (("a",1),Ctx_node("a",[Ctx_hole(1,1)]))
let rule3_ID = (("b",1),Ctx_node("b",[Ctx_hole(1,1)]))
let rule4_ID = (("#",1),Ctx_node("#",[]))

let (trans_ex:dtop_transducer) = {sigin = sig1 ; 
                                sigout = sig2 ; 
                                nbstates = 1 ; 
                                axiom = ax ; 
                                rules = [rule1;rule2;rule3;rule4]}

let (trans_id:dtop_transducer) = {sigin = sig1 ; 
                                sigout = sig1 ; 
                                nbstates = 1 ; 
                                axiom = ax ; 
                                rules = [rule1_ID;rule2_ID;rule3_ID;rule4_ID]}

let (tree_ex:ranked_tree) = (sig1,root_ex)

let t1 = trans_of_xml "transducer_c1.xml"
let t2 = trans_of_xml "transducer_c2.xml"

let t3 = compose_noDI t1 t2

(* Exemples d'automates de domaine *)

let trans_DI = trans_of_xml "transducer_DI1.xml"
and trans_DI_2 = trans_of_xml "transducer_DI2.xml"
and tree_DI_1 = tree_of_xml "tree_DI_1.xml"
and tree_DI_2 = tree_of_xml "tree_DI_2.xml"

let aut_DI_1 = make_DI_automaton trans_DI
and aut_DI_2 = make_DI_automaton trans_DI_2
and aut_DI_3 = make_DI_automaton t3

(* Intersection et minimisation d'automates *)

let signature = [("f",2);("a",1);("b",1);("#",0)]
let rules = [
  (("f",1),[2;3]);
  (("a",2),[4]);
  (("a",4),[6]);
  (("a",6),[2]);
  (("b",2),[4]);
  (("b",4),[6]);
  (("b",6),[2]);
  (("#",2),[]);
  
  (("a",3),[3]);
  (("a",5),[3]);
  (("b",3),[5]);
  (("b",5),[5]);
  (("#",3),[]);
  (("#",5),[])  
]

let rules_inter1 = [
  (("a",1),[2]);
  (("a",2),[2]);
  (("b",2),[2]);
  (("#",2),[])
]

let rules_inter2 = [
  (("a",1),[2]);
  (("b",1),[2]);
  (("b",2),[3]);
  (("a",3),[3]);
  (("b",3),[3]);
  (("#",3),[])
]

let aut_to_minimize = {
  signature = signature;
  nbstates = 6;
  initstate = 1;
  rules = rules
}

let aut_inter1 = {
  signature;
  nbstates = 2;
  initstate = 1;
  rules = rules_inter1
}

let aut_inter2 = {
  signature;
  nbstates = 3;
  initstate = 1;
  rules = rules_inter2
}

let aut_inter = minimize_automaton (automata_intersection aut_inter1 aut_inter2)

(* Composition avec inspection de domaine *)

let t3_DI = compose_DI (make_DI_automaton t1,t1) (make_DI_automaton t2,t2)

let trans_comp_1 = trans_of_xml "transducer_DI3.xml"
let trans_comp_2 = trans_of_xml "transducer_DI4.xml"
let trans_comp_3 = trans_of_xml "transducer_DI5.xml"

let aut_comp_1 = make_DI_automaton trans_comp_1
let aut_comp_2 = make_DI_automaton trans_comp_2
let aut_comp_3 = make_DI_automaton trans_comp_3

let trans_compA = compose_DI (aut_comp_1,trans_comp_1) (aut_comp_2,trans_comp_2)
let trans_compB = compose_DI (aut_comp_1,trans_comp_1) (aut_comp_3,trans_comp_3)

(* Composition install/desinstall*)

let trans_ins_1 = trans_of_xml "trans_ins_1.xml"
let trans_des_1 = trans_of_xml "trans_des_1.xml"

let aut_ins_1 = make_DI_automaton trans_ins_1
let aut_des_1 = make_DI_automaton trans_des_1

let (aut_comp,trans_comp) = compose_DI (aut_ins_1,trans_ins_1) (aut_des_1,trans_des_1)

let trans_late = trans_of_xml "trans_late.xml"
let trans_normal = normal_form (make_DI_automaton trans_late,trans_late)

(* Test d'identité *)
let trans_ID = make_ID_transducer trans_comp.sigin
let eq = trans_equality (make_DI_automaton trans_ID,trans_ID) (aut_comp,trans_comp)

(* Tests génération automatique *)
let path = "/3_1/2_2"
let p = decompose_path path 

let trans_install = make_trans_install 3 2 path
let trans_uninstall = make_trans_uninstall 3 2 path
let aut_DI = make_DI_automaton trans_install

let (aut_comp,trans_comp) = compose_DI (aut_DI,trans_install) (make_DI_automaton trans_uninstall,trans_uninstall)

let trans_ID = make_ID_transducer trans_install.sigin
let eq = trans_equality (aut_DI,trans_ID) (aut_comp,trans_comp)

*)



