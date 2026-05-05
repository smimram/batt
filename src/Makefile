all: test

build:
	@dune exec ./batt.exe

test:
	@dune exec ./batt.exe test.batt

explain:
	cat ../_build/default/src/parser.conflicts
