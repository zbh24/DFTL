#############################################################
#                                                           #
#    GNUMakefile for coq code                               #
#                                                           #
#        by Guo Yu					    #
#    	 1.1beta           				    #
#        - 2014-05-03                                       #
#                                                           #
#############################################################

SHELL = /bin/bash
ECHO := /bin/echo

COQC := $(COQBIN)coqc
COQFLAGS = $(COQLIBS)
COQDEP := $(COQBIN)coqdep
COQDOC := $(COQBIN)coqdoc
GALLINA := $(COQBIN)gallina

COQLIBS := -I .

.PHONY: noargs FORCE

noargs :
	@echo "1> make deploy first"
	@echo "2> make all"
FORCE: ;

###########################################
#   Source Code
###########################################

SRC := $(wildcard *.v)

###########################################
#   Modules
###########################################

# .PHONY: modules

# mods.inc:
# 	@$(ECHO) -n 'MOD :='> $@
# 	@find -type d ! -name '.' | grep -v '.svn' | grep -v 'CVS' \
# 	| sed -e 's/^\.\///g' | xargs echo -n >> $@

# -include mods.inc

# MOD_MK := $(patsubst %, %/module.mk, $(MOD))
# MOD_MK2 := $(patsubst %, %/makefile, $(MOD))

# %/module.mk:
# 	@$(ECHO) "generating $@ ..."
# 	@$(ECHO) "MODULE := $*" > $@
# 	@$(ECHO) 'SRC += $$(wildcard $$(MODULE)/*.v)' >> $@
# 	@$(ECHO) 'COQLIBS += -I $$(MODULE) ' >> $@
# 	@$(ECHO) "generating $*/makefile ..."
# 	@$(ECHO) "include module.mk" > $*/makefile
# 	@$(ECHO) -e '\n.PHONY: all FORCE\n' >> $*/makefile
# 	@$(ECHO) -e 'SRC := $$(wildcard *.v)\n' >> $*/makefile
# 	@$(ECHO) -e 'OBJ := $$(SRC:.v=.vo)\n' >> $*/makefile
# 	@$(ECHO) -e 'all: $$(OBJ) ;\n' >> $*/makefile
# 	@$(ECHO) -e 'FORCE: ;\n' >> $*/makefile
# 	@$(ECHO) -e '%.vo: FORCE \n\tmake -C $(shell echo "$*" \
# 	| sed -e "s/[^/]\+/../g") $$(MODULE)/$$@' >> $*/makefile
# 	@$(ECHO) -e '\ntestmk:\n\tmake -f module.mk\n' >> $*/makefile
# 	@$(ECHO) -e '\nclean:\n\trm -f *.vo *.d\n\trm -f *.html\n' >> $*/makefile

# -include $(MOD_MK)

###########################################
#   Objective File
###########################################

DEP := $(SRC:.v=.d)
OBJ := $(SRC:.v=.vo)
SPEC := $(SRC:.v=.vi)
GOBJ := $(SRC:.v=.g)
GLOBOBJ := $(SRC:.v=.glob)
HTML := $(SRC:.v=.html)
GHTML := $(SRC:.v=.g.html)

.PHONY: test
test:
	@echo "######################################################"
	@echo -n "MOD = "
	@echo $(MOD)
	@echo "MAIN_MOD = " $(MAIN_MOD)
	@echo -n "Modules Makfile = "
	@echo $(MOD_MK)
	@echo -n "SRC = "
	@echo $(SRC)
	@echo -n "OBJ = "
	@echo $(OBJ)
	@echo -n "VMOD = "
	@echo $(VMOD)
	@echo -n "MODRPATH = "
	@echo $(MODRPATH)
	@echo -n "COQFLAGS = "
	@echo $(COQFLAGS)

###########################################
#    Special targets
###########################################

.PHONY: all depends

all : $(OBJ)

%.vo:	%.v %.d
	$(COQC) $(COQFLAGS) $<

%.d:	%.v
	$(COQDEP) $(COQFLAGS) $< > $@

%.g: 	%.v
	$(GALLINA) $<

# %.tex: %.g
# 	$(COQDOC) -latex -g $< -o $@

# %.html: %.g
# 	$(COQDOC) -html -g $< -o $@

-include $(DEP)

###########################################
#  User-defined targets
###########################################

#.PHONY: ocap
#pcap: ocap/ocap.vo

###########################################
#  deploy makefile
###########################################

.PHONY: deploy
deploy: 
	make depends

###########################################
#   clean
###########################################

.PHONY: archclean clean

clean:
	rm -f $(OBJ)
	rm -f $(DEP)
	rm -f $(GLOBOBJ)
	#rm -f $(HTMLFILES) $(GHTMLFILES)

archclean: 
	rm -f *.cmx *.o *.vo *.glob *.d
	rm -f $(MOD_MK) $(MOD_MK2)
	rm -f mods.inc

