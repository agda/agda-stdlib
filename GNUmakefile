AGDA_EXEC ?= agda
AGDA_OPTIONS=-Werror
AGDA_RTS_OPTIONS=+RTS -M4.0G -H3.5G -A128M -RTS
AGDA=$(AGDA_EXEC) $(AGDA_OPTIONS) $(AGDA_RTS_OPTIONS)
CABAL_EXEC ?= cabal
CABAL_RUN_COMMAND=$(CABAL_EXEC) run

# Before running `make test` the `fix-whitespace` program should
# be installed:
#
#   cabal install fix-whitespace

test: doc/Everything.agda check-whitespace
	cd doc && $(AGDA) README.agda

testsuite:
	$(MAKE) -C tests test AGDA="$(AGDA)" AGDA_EXEC="$(AGDA_EXEC)" only=$(only)

fix-whitespace:
	$(CABAL_EXEC) exec -- fix-whitespace

check-whitespace:
	$(CABAL_EXEC) exec -- fix-whitespace --check

setup: doc/Everything.agda

.PHONY: doc/Everything.agda
doc/Everything.agda:
	$(CABAL_RUN_COMMAND) GenerateEverything -- --out-dir doc

.PHONY: listings
listings: doc/Everything.agda
	cd doc && $(AGDA) --html README.agda -v0

clean :
	find . -type f -name '*.agdai' -delete
	rm -f doc/Everything.agda doc/EverythingSafe.agda
