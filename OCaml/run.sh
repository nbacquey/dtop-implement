#!/bin/bash

EXT_PACKAGES="xml-light.cma str.cma unix.cma"
LOADING_ORDER=" Utils.cmo Timer.cmo DTOP_Transducers.cmo IO_xml.cmo DTT_Automata.cmo Operations.cmo Generators.cmo Testing.cmo Default_Structures.cmo STree.cmo SDTOP.cmo"

./compile.sh
echo ====================================
ledit ocaml  -init main.ml -I `ocamlfind query xml-light` -I _build $EXT_PACKAGES $LOADING_ORDER