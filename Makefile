all: build

build:
	@dune build

test:
	@dune runtest -f

.PHONY: test
