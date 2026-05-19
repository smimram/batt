all: test

build:
	@dune build

test:
	@dune exec ./batt.exe -- test.batt

explain:
	@cat ../_build/default/src/parser.conflicts
