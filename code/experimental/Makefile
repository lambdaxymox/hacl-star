include ../../Makefile.include

DIRECTORIES=

%-c: %
	$(MAKE) -C $< extract-c

%-clean: %
	$(MAKE) -C $< clean

extract-c: $(addsuffix -c, $(DIRECTORIES))

test:
	@echo "No tests for Experimental here"

all-ci:

all-ct:

clean: $(addsuffix -clean, $(DIRECTORIES))
	rm -rf *~ *.exe *.out *.graph
