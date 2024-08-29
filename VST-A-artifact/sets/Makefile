CURRENT_DIR=.

-include CONFIGURE

COQC=$(COQBIN)coqc$(EXESUF)
COQDEP=$(COQBIN)coqdep$(EXESUF)

COQ_FLAG = -Q $(CURRENT_DIR) SetsClass
DEP_FLAG = -Q $(CURRENT_DIR) SetsClass

FILES = \
  SetsClass.v \
  SetsDomain.v \
  SetElement.v \
  RelsDomain.v \
  SetProd.v

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

all: .depend $(FILES:%.v=%.vo)

depend: .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f *.vo *.glob *.vos *.vok .*.aux

.DEFAULT_GOAL := all

include .depend
