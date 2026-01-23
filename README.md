These are the lecture notes for COMP2065 (IFR) using lean4 and verso.

Run
lake exe cache get
lake exe ifrnotes
and then 
cd _out/html-multi
python3 -m http.server 8000
open http://localhost:8000

if anchors are stuck:
rm -rf .lake/build/highlighted

To generate a PDF via LaTeX, run:
```
lake exe cache get
lake exe ifrnotes
latexmk -cd -lualatex -interaction=nonstopmode _out/tex/main
```
