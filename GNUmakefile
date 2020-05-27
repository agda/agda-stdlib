AGDA_EXEC=agda
RTS_OPTIONS=+RTS -M4.0G -H3.5G -A128M -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)

# Before running `make test` the `fix-whitespace` program should
# be installed:
#
#   git clone git@github.com:agda/fix-whitespace --depth 1
#   cd fix-whitespace
#   cabal install

test: Everything.agda check-whitespace
	$(AGDA) -i. -isrc README.agda

check-whitespace:
	cabal v1-exec -- fix-whitespace --check

setup: Everything.agda

.PHONY: Everything.agda
Everything.agda:
# The command `cabal build` is needed by cabal-install 3.0.0.0 and the
# command `cabal install` is needed by cabal-install <= 2.4.*. I did
# not found any problem running both commands with different versions
# of cabal-install. See Issue #1001.
	cabal v1-clean && cabal v1-build && cabal v1-install
	cabal v1-exec -- GenerateEverything

.PHONY: listings
listings: Everything.agda
	$(AGDA) -i. -isrc --html README.agda -v0

clean :
	find . -type f -name '*.agdai' -delete
