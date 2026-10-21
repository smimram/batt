MD = $(wildcard *.md)
HTML = $(MD:.md=.html)

all: html

html: $(HTML)

%.html: %.md batt.css
	pandoc -s -M lang=en --toc --shift-heading-level-by=-1 --css=batt.css $< -o $@
