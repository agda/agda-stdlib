AGDA_EXEC ?= agda
AGDA_OPTIONS=-Werror
AGDA_RTS_OPTIONS=+RTS -M4.0G -H3.5G -A128M -RTS
AGDA=$(AGDA_EXEC) $(AGDA_OPTIONS) $(AGDA_RTS_OPTIONS)

# Before running `make test` the `fix-whitespace` program should
# be installed:
#
#   cabal install fix-whitespace

test: Everything.agda check-whitespace
	cd doc && $(AGDA) README.agda

testsuite:
	$(MAKE) -C tests test AGDA="$(AGDA)" AGDA_EXEC="$(AGDA_EXEC)" only=$(only)

fix-whitespace:
	cabal exec -- fix-whitespace

check-whitespace:
	cabal exec -- fix-whitespace --check

setup: Everything.agda

.PHONY: Everything.agda
Everything.agda:
	cabal run GenerateEverything -- --out-dir doc

.PHONY: listings
listings: Everything.agda
	cd doc && $(AGDA) --html README.agda -v0

clean :
	find . -type f -name '*.agdai' -delete
	rm -f Everything.agda EverythingSafe.agda
