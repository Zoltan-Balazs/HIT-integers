.PHONY: thesis

defense:
	 cd thesis/defense && pdflatex --shell-escape defense.tex

thesis:
	 cd thesis && pdflatex --interaction nonstopmode -halt-on-error -file-line-error --shell-escape thesis.tex && biber thesis && pdflatex --interaction nonstopmode -halt-on-error -file-line-error --shell-escape thesis.tex && pdflatex --shell-escape thesis.tex
