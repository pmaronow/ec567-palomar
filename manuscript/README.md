# Manuscript

[Read the PDF](ec_ranks_5_7.pdf). The complete TeX sources, bibliography, and
three certificate programs with their JSON inputs are in [source/](source).

Appendix A identifies `https://github.com/pmaronow/ec567-palomar` as the planned
repository home and gives the paths of the verification programs. All other
manuscript source files are unchanged from the supplied archive.

To rebuild the PDF with a TeX installation providing `latexmk`, `pdflatex`,
and the packages used by the manuscript:

```sh
cd manuscript/source
latexmk -norc -pdf -pdflatex='pdflatex -no-shell-escape %O %S' main.tex
cp main.pdf ../ec_ranks_5_7.pdf
```

The supplied `source/build.py` additionally runs the three Python certificate
programs before compiling the paper. The Lean formalization and its verification
instructions are in the repository root.
