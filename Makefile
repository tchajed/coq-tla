SRC_DIRS := 'src' 'external'
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")
PROJ_VFILES := $(shell find 'src' -name "*.v")
DOC_VFILES := $(PROJ_VFILES:src/%.v=docs/%.html)

COQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e 's/-arg ([^ ]*)/\1/g' _CoqProject)
COQPROJECT_Q_ARGS := $(shell grep '^-Q' _CoqProject)

default: $(PROJ_VFILES:.v=.vo)

doc: $(DOC_VFILES)


.coqdeps.d: $(ALL_VFILES) _CoqProject
	@echo "COQDEP $@"
	@coqdep -f _CoqProject $(ALL_VFILES) > $@

ifneq ($(MAKECMDGOALS), clean)
-include .coqdeps.d
endif

%.vo: %.v _CoqProject
	@echo "COQC $<"
	@coqc $(COQPROJECT_ARGS) $< -o $@

docs:
	@mkdir -p docs

docs/%.html: src/%.v src/%.vo | docs
	@echo "ALECTRYON $<"
	@alectryon --long-line-threshold 80 $(COQPROJECT_Q_ARGS) --frontend coq+rst --backend webpage $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	@rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.glob)
	@find $(SRC_DIRS) -name ".*.aux" -exec rm {} \;
	rm -rf docs
	rm -f .coqdeps.d

.PHONY: default clean docs
.DELETE_ON_ERROR:
