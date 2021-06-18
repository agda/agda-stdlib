INTERACTIVE ?= --interactive

runtests: runtests.agda
	rm -f _build/runtests
	rm -f _build/MAlonzo/Code/Qruntests*
	$(AGDA) --compile-dir=_build/ -c runtests.agda

test: runtests
	./_build/runtests $(AGDA_EXEC) $(INTERACTIVE) --timing --failure-file failures --only $(only)


retest: runtests
	./_build/runtests $(AGDA_EXEC) $(INTERACTIVE) --timing --failure-file failures --only-file failures --only $(only)
