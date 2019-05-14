AGDA_EXEC=agda
RTS_OPTIONS=+RTS -M2.5G -H2.5G -A128M -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)

# Before running `make test` the `fix-agda-whitespace` program should
# be installed:
#
#   cd agda-development-version-path/src/fix-agda-whitespace
#   cabal install

test: Everything.agda check-whitespace
	$(AGDA) -i. -isrc README.agda

check-whitespace:
	cabal exec -- fix-agda-whitespace --check

setup: Everything.agda

.PHONY: Everything.agda
Everything.agda:
	cabal clean && cabal install
	cabal exec -- GenerateEverything

.PHONY: listings
listings: Everything.agda
	$(AGDA) -i. -isrc --html README.agda -v0

clean :
	find . -type f -name '*.agdai' -delete
