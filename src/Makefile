all: test

build:
	@dune build

test:
	$(MAKE) -C ../bin $@

explain: build
	@cat ../_build/default/src/parser.conflicts
