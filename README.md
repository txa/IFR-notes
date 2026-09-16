These are the lecture notes for COMP2065 (IFR) using lean4 and verso.

Run
lake exe cache get
lake exe ifrnotes
and then 
cd _out/html-multi
python3 -m http.server 8000
open http://localhost:8000

Or just run ./preview.sh (optionally ./preview.sh <port>) to build, serve, and
open the browser in one step. The server runs detached in the background, so
it keeps running even if you close the terminal. Stop it with
./preview.sh --stop (optionally ./preview.sh --stop <port>).

if anchors are stuck:
rm -rf .lake/build/highlighted