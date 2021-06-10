runtests: runtests.agda
	$(AGDA) -c runtests.agda

test: runtests
	./runtests $(AGDA_EXEC) --interactive --timing --failure-file failures


retest: runtests
	./runtests $(AGDA_EXEC) --interactive --timing --failure-file failures --only-file failures
