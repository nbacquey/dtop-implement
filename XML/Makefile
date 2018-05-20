#######################
##     Variables     ##
#######################

SAXON = java -jar saxon9he.jar

TREE_DIR = ./Trees
TRANS_DIR = ./Transducers

DTDCHECK = xmllint --dtdvalid
DTDTREE := $(DTDCHECK) $(TREE_DIR)/tree.dtd
DTDTRANS := $(DTDCHECK) $(TRANS_DIR)/transducer.dtd

TREE_LIST := $(shell ls $(TREE_DIR)/*.xml)
TRANS_LIST := $(shell ls $(TRANS_DIR)/*.xml)

CONVERTER_FILE = transducer_XML_to_XSLT.xsl

XML_TO_XSLT := $(SAXON) -xsl:$(CONVERTER_FILE) 

################
##     ALL    ##
################

all: validate transducers_to_xslt

#############################
##     File validation     ##
#############################

validate: tree_validate_all trans_validate_all
	@echo ''Validation terminée''

tree_validate_all: dtd_tree_validate_all schema_tree_validate_all
	@echo ''Arbres validés''
	
trans_validate_all: dtd_trans_validate_all schema_trans_validate_all
	@echo ''Transducteurs validés''
	
dtd_tree_validate_all:
	@$(foreach file,$(TREE_LIST),$$($(DTDTREE) $(file) 1> /dev/null))
	
schema_tree_validate_all: 
	@echo ''ok''

dtd_trans_validate_all:
	@$(foreach file,$(TRANS_LIST),$$($(DTDTRANS) $(file) 1> /dev/null))
	
schema_trans_validate_all:
	@echo ''ok''
	
tree_validate:
	@$$($(DTDTREE) $(TREE) 1> /dev/null)
	
trans_validate:
	@$$($(DTDTRANS) $(TRANS) 1> /dev/null)

#################################
##     File transformation     ##
#################################

transducers_to_xslt: 
	@$(foreach file,$(TRANS_LIST),$$($(XML_TO_XSLT) -s:$(file) -o:$(subst .xml,.xsl,$(file))))
	@echo ''Transducteurs convertis en XSLT''
	
apply:
	@$$($(SAXON) -xsl:$(TRANS_DIR)/$(TRANS).xsl -s:$(TREE_DIR)/$(TREE).xml -o:$(TREE_DIR)/$(TREE)_by_$(TRANS).xml)
	


