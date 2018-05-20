open Utils
open DTOP_Transducers
open DTT_Automata
open IO_xml
open Operations
open Generators
open Testing
open Timer
open SDTOP
(**
(* Quelques exemples *)

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
            
let (tree1:ranked_tree) = (signature,root1) and
    (tree2:ranked_tree) = (signature,root2) and
    (tree3:ranked_tree) = (signature,root3) 



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
**)


let _ = 
  parse_conf_file (Sys.argv.(1));
  output_results()



