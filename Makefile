all: build

build:
	@dune build

test:
	@dune runtest -f

clean:
	$(MAKE) -C stdlib $@
	$(MAKE) -C graytt $@

.PHONY: test
