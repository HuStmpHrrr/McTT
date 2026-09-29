.PHONY: all pretty-timed test coqdoc clean depgraphdoc

# The OCaml driver needs the code extracted from [Entrypoint.v]; while that file
# is left out of [_CoqProject], only the Rocq development is built, and a
# generated top-level [dune] file hides [driver/] from [dune build]/[dune runtest].
ENTRYPOINT_ENABLED := $(shell grep -qx '\./Entrypoint\.v' theories/_CoqProject && echo yes)

.PHONY: driver-gate
ifeq ($(ENTRYPOINT_ENABLED),yes)
DUNE_BUILD := dune build
driver-gate:
	@rm -f dune
else
DUNE_BUILD := echo "SKIP dune build: Entrypoint.v is not in _CoqProject"
driver-gate:
	@echo "SKIP driver: Entrypoint.v is not in _CoqProject"
	@printf '(dirs :standard \\ driver)\n' > dune
endif

all: driver-gate
	@$(MAKE) -C theories
	@$(DUNE_BUILD)

pretty-timed: driver-gate
	@$(MAKE) pretty-timed -C theories
	@$(DUNE_BUILD)

coqdoc:
	@${MAKE} coqdoc -C theories

depgraphdoc:
	@$(MAKE) depgraphdoc -C theories

clean:
	@$(MAKE) clean -C theories
	@dune clean
	@echo "Cleaning finished."
