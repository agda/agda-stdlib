runtests: runtests.agda
	rm _build/runtests
	rm _build/MAlonzo/Code/Qruntests*
	$(AGDA) --compile-dir=_build/ -c runtests.agda

test: runtests
	./_build/runtests $(AGDA_EXEC) --interactive --timing --failure-file failures


retest: runtests
	./_build/runtests $(AGDA_EXEC) --interactive --timing --failure-file failures --only-file failures
