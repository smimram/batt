all: test

build:
	@dune build

test:
	@dune exec ./batt.exe test.batt
	@dune exec ./batt.exe bunch.batt

explain:
	@cat ../_build/default/src/parser.conflicts
