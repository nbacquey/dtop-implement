#!/bin/bash

EXT_PACKAGES="xml-light.cma str.cma unix.cma"
LOADING_ORDER="Default_Structures.cmo Utils.cmo DTTA.cmo DTOP.cmo  Generators.cmo Operations.cmo Equivalence.cmo Examples.cmo"

./compile.sh
echo ====================================
ledit ocaml  -init main.ml -I `ocamlfind query xml-light` -I _build $EXT_PACKAGES $LOADING_ORDER