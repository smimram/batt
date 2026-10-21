MD = $(wildcard *.md)
HTML = $(MD:.md=.html)

all: html

html: $(HTML)

%.html: %.md
	pandoc $< -o $@
