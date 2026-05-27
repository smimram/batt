all: test

build:
	@dune build

test:
	@dune exec ./batt.exe -- -I ../stdlib test.batt

explain: build
	@cat ../_build/default/src/parser.conflicts
