open List
open Printf
open Utils
open DTOP_Transducers

(* Fonctions I/O *)

let tree_dir = "../Trees/"
let trans_dir = "../Transducers/"

let xml_header = "<?xml version=\"1.0\" encoding=\"utf-8\"?>"
let tree_header = "<!DOCTYPE tree SYSTEM \"tree.dtd\">"
let trans_header = "<!DOCTYPE transducer SYSTEM \"transducer.dtd\">"
  
let xmlOpenTree file = Xml.parse_file (tree_dir^file)
let xmlOpenTrans file = Xml.parse_file (trans_dir^file)

let xml_tree_output x file =
  let oc = open_out (tree_dir^file) in 
  fprintf oc "%s\n%s\n%s" xml_header tree_header (Xml.to_string_fmt x);
  close_out oc
  
let xml_trans_output x file =
  let oc = open_out (trans_dir^file) in 
  fprintf oc "%s\n%s\n%s" xml_header trans_header (Xml.to_string_fmt x);
  close_out oc

  
let extract_symbol = function
  | Xml.PCData(_) -> null_symb
  | Xml.Element(_,[],_) -> null_symb
  | Xml.Element(_,_::[],_) -> null_symb
  | Xml.Element(_,(att1::(att2::_)),_) -> 
    let atts = [att1;att2] in 
    (assoc "NAME" atts, int_of_string(assoc "ARITY" atts))  

let extract_signature = function 
  | Xml.PCData(_) -> null_sig
  | Xml.Element(_,_,symbols) -> 
    ((fold_left (fun a b -> (extract_symbol b)::a) [] symbols):signature)

let rec extract_node = function
  | Xml.PCData(_) -> null_node
  | Xml.Element(_,[],_) -> null_node
  | Xml.Element(_,atts,children) -> 
    Node(
      assoc "SYMBOL" atts,
      fold_right (fun b a -> (extract_node b)::a) children []
    )
  
let extract_states = function
  |Xml.PCData(_) -> 1
  |Xml.Element(_,_,states) -> length states
  
let rec extract_context = function
  |Xml.PCData(_) -> null_ctx
  |Xml.Element(name,atts,children) ->  
    if name = "call"
    then
      Ctx_hole(
        int_of_string(assoc "STATE" atts), 
        int_of_string(assoc "VARIABLE" atts)
      )
    else
      Ctx_node(
        assoc "SYMBOL" atts, 
        fold_right (fun b a -> (extract_context b)::a) children []
      )
      
let extract_axiom = function
  |Xml.PCData(_) -> null_ctx
  |Xml.Element(_,_,node::_) -> extract_context node
  |Xml.Element(_,_,_) -> null_ctx
  
let extract_rule = function
  | Xml.PCData(_) -> null_rule
  | Xml.Element(_,_,[]) -> null_rule
  | Xml.Element(_,atts,context::_) -> 
    (
      (assoc "SYMBOL" atts, int_of_string(assoc "STATE" atts)),
      extract_context context
    )
  
let extract_rules = function
  | Xml.PCData(_) -> []
  | Xml.Element(_,_,rules) -> 
    fold_left (fun a b -> (extract_rule b)::a) [] rules

let xml_to_internal_tree = function
  | Xml.PCData(_) -> null_tree
  | Xml.Element(_,_,[]) -> null_tree
  | Xml.Element(_,_,_::[]) -> null_tree
  | Xml.Element(_,_,(signature::(node::_))) -> 
    ((extract_signature signature,extract_node node):ranked_tree)
  
let xml_to_internal_transducer = function
  | Xml.PCData(_) -> null_trans
  | Xml.Element(_,_,[sigin;sigout;states;axiom;rules]) -> 
    {sigin = (extract_signature sigin);
     sigout = (extract_signature sigout);
     nbstates = (extract_states states);
     axiom = (extract_axiom axiom);
     rules = (extract_rules rules)
    }
  | Xml.Element(_,_,_) -> null_trans
  
  
let make_xml_signature signature = 
  Xml.Element("signature",
              [],
              (fold_left 
                (
                  fun  a (symb,arity) -> 
                    (
                      Xml.Element("symbol",
                                  [("name",symb);("arity",string_of_int arity)],[]
                      )
                    )::a
                )
                []
                signature
                )
              )
  
let rec make_xml_node (Node(symb,children)) = 
  Xml.Element(
              "node",
              [("symbol",symb)],
              (fold_right
                (fun node a -> (make_xml_node node)::a)
                children
                []
              )
             )
              
let rec make_xml_context = function 
  | Ctx_node(symb,children) -> 
    Xml.Element(
      "context",
      [("symbol",symb)],
      (fold_right
        (fun context a -> (make_xml_context context)::a)
        children
        []
      )
    )
  
  | Ctx_hole(state,childnum) -> 
    Xml.Element(
      "call",
      [("state",string_of_int state);("variable",string_of_int childnum)],
      []
    )
  
let make_xml_states n =
  let statelist = (
    fold_left 
      (fun a b -> 
        (Xml.Element("state",[("name",string_of_int b)],[]))::a
      ) 
      [] 
      (range n)
  ) in
  Xml.Element("states",[],statelist)
  
let make_xml_axiom ctx = 
  Xml.Element("axiom",[],[make_xml_context ctx])
  
let make_xml_rule ((symb,state),context) =
  Xml.Element(
    "rule",
    [("symbol",symb);("state",string_of_int state)],
    [make_xml_context context]
  )
  
let make_xml_rules rules = 
  let rulelist = (fold_left (fun a b -> (make_xml_rule b)::a) [] rules) in
  Xml.Element("rules",[],rulelist)
  
let internal_tree_to_xml = function
  | (signature,node) -> 
    Xml.Element(
      "tree",
      [],
      [make_xml_signature signature ; make_xml_node node]
    )
  
let internal_transducer_to_xml trans =
  let make_sigin = function
    |Xml.PCData(_) -> Xml.PCData("")
    |Xml.Element(_,_,children) -> Xml.Element("signature-in",[],children)
  and make_sigout = function
    |Xml.PCData(_) -> Xml.PCData("")
    |Xml.Element(_,_,children) -> Xml.Element("signature-out",[],children) in
    
  let sigin = make_sigin(make_xml_signature trans.sigin) 
  and sigout = make_sigout(make_xml_signature trans.sigout) 
  and states = (make_xml_states trans.nbstates) 
  and axiom = (make_xml_axiom trans.axiom) 
  and rules = (make_xml_rules trans.rules) in
  Xml.Element("transducer",[],[sigin;sigout;states;axiom;rules])
  
(* Fonctions I/O terminales *)  

let tree_of_xml file = xml_to_internal_tree (xmlOpenTree file)

let xml_of_tree tree file = xml_tree_output (internal_tree_to_xml tree) file

let trans_of_xml file = xml_to_internal_transducer (xmlOpenTrans file)

let xml_of_trans trans file = xml_trans_output (internal_transducer_to_xml trans) file

