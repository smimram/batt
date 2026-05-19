all: test

build:
	@dune build

test:
	@dune exec ./batt.exe -- -I ../stdlib test.batt

explain:
	@cat ../_build/default/src/parser.conflicts
