INTERACTIVE   ?= --interactive
GHC_EXEC      ?= ghc
CABAL         ?= cabal
CABAL_OPTIONS ?= --with-compiler $(GHC_EXEC)

runtests: runtests.agda
	rm -f _build/runtests
	rm -f _build/MAlonzo/Code/Qruntests*
	$(AGDA) --compile-dir=_build/ -c --ghc-dont-call-ghc runtests.agda
	$(CABAL) build $(CABAL_OPTIONS)

test: runtests
	$(CABAL) exec $(CABAL_OPTIONS) runtests -- $(AGDA_EXEC) $(INTERACTIVE) --timing --failure-file failures --only $(only)


retest: runtests
	$(CABAL) exec $(CABAL_OPTIONS) runtests -- $(AGDA_EXEC) $(INTERACTIVE) --timing --failure-file failures --only-file failures --only $(only)
