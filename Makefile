SRC_DIRS := 'src' 'external'
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")
PROJ_VFILES := $(shell find 'src' -name "*.v")

COQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e 's/-arg ([^ ]*)/\1/g' _CoqProject)

default: $(PROJ_VFILES:.v=.vo)

.coqdeps.d: $(ALL_VFILES) _CoqProject
	@echo "COQDEP $@"
	@coqdep -f _CoqProject $(ALL_VFILES) > $@

ifneq ($(MAKECMDGOALS), clean)
-include .coqdeps.d
endif

%.vo: %.v
	@echo "COQC $<"
	@coqc $(COQARGS) $(shell cat '_CoqProject') $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	@rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.glob)
	@find $(SRC_DIRS) -name ".*.aux" -exec rm {} \;
	rm -f .coqdeps.d

.PHONY: default clean
.DELETE_ON_ERROR:
