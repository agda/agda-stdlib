AGDA_EXEC ?= agda
AGDA_OPTIONS=-Werror
AGDA_RTS_OPTIONS=+RTS -M4.0G -H3.5G -A128M -RTS
AGDA=$(AGDA_EXEC) $(AGDA_OPTIONS) $(AGDA_RTS_OPTIONS)

# Before running `make test` the `fix-whitespace` program should
# be installed:
#
#   cabal install fix-whitespace

test: Everything.agda check-whitespace
	$(AGDA) -i. -isrc README.agda

testsuite:
	$(MAKE) -C tests test AGDA="$(AGDA)" AGDA_EXEC="$(AGDA_EXEC)" only=$(only)

check-whitespace:
	cabal exec -- fix-whitespace --check

setup: Everything.agda

.PHONY: Everything.agda
Everything.agda:
# The command `cabal build` is needed by cabal-install 3.0.0.0 and the
# command `cabal install` is needed by cabal-install <= 2.4.*. I did
# not found any problem running both commands with different versions
# of cabal-install. See Issue #1001.
	cabal run GenerateEverything

.PHONY: listings
listings: Everything.agda
	$(AGDA) -i. -isrc --html README.agda -v0

clean :
	find . -type f -name '*.agdai' -delete
