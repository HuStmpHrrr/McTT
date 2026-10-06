.PHONY: all pretty-timed test coqdoc clean depgraphdoc homepage

all:
	@$(MAKE) -C theories
	@dune build --root .

pretty-timed:
	@$(MAKE) pretty-timed -C theories
	@dune build --root .

coqdoc:
	@${MAKE} coqdoc -C theories

depgraphdoc:
	@$(MAKE) depgraphdoc -C theories

# The site deployed to GitHub pages, in $(HOMEPAGE): the README as the index
# page, the coqdoc pages, the dependency graph, and the library pages
# (lib/index.html), highlighted, every use linked to its definition.  Builds
# whatever is not built yet.
HOMEPAGE := html
PANDOC := pandoc
HOMEPAGE_TITLE := McTT: Building A Correct-By-Construction Proof Checkers For Type Theories

homepage:
	@$(MAKE) all
	@$(MAKE) coqdoc
	@$(MAKE) depgraphdoc
	@echo "HOMEPAGE $(HOMEPAGE)"
	@rm -rf "$(HOMEPAGE)"
	@cp -R theories/html "$(HOMEPAGE)"
	@cp theories/dep.html "$(HOMEPAGE)/dep.html"
	@cp assets/styling.css "$(HOMEPAGE)/styling.css"
	@cp -R assets/images "$(HOMEPAGE)/images"
	@dune exec --root . mctt-doc -- lib "$(HOMEPAGE)/lib"
# The README's links are absolute as GitHub renders it, but relative once it
# is the deployed index.
	@sed -e 's!\[Coqdoc\](https://[A-Za-z0-9.-]*\.github\.io/McTT/dep\.html)![Coqdoc](dep.html)!' \
	     -e 's!(https://[A-Za-z0-9.-]*\.github\.io/McTT/lib/index\.html)!(lib/index.html)!' README.md \
	  | $(PANDOC) -f markdown -H assets/include.html --no-highlight --metadata pagetitle='$(HOMEPAGE_TITLE)' \
	      -t html --css styling.css -o "$(HOMEPAGE)/index.html"

clean:
	@$(MAKE) clean -C theories
	@dune clean --root .
	@rm -rf "$(HOMEPAGE)"
	@echo "Cleaning finished."
