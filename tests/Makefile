INTERACTIVE   ?= --interactive
GHC_EXEC      ?= ghc
CABAL         ?= cabal
CABAL_OPTIONS ?= --with-compiler $(GHC_EXEC)

AGDA_BUILD_DIR  = _config/_build
CABAL_BUILD_DIR = _config/dist-newstyle

./runtests: admin/runtests/Main.agda
	cd admin/runtests && AGDA="$(AGDA)" sh run

test: ./runtests
	./runtests "$(AGDA)" $(INTERACTIVE) --timing --failure-file failures --only $(only)


retest: ./runtests
	./runtests "$(AGDA)" $(INTERACTIVE) --timing --failure-file failures --only-file failures --only $(only)
