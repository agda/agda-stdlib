runtests: runtests.agda
	$(AGDA) --compile-dir=_build/ -c runtests.agda

test: runtests
	./runtests $(AGDA_EXEC) --interactive --timing --failure-file failures


retest: runtests
	./runtests $(AGDA_EXEC) --interactive --timing --failure-file failures --only-file failures
