#!/bin/bash

./../cadet -c tmp.aig $1

#aigtoaig tmp.aag tmp.aig

# abc -c "read tmp.aig; write tmp.aig"
abc -c "read tmp.aig; dc2; dc2; write tmp.aig"
# abc -c "read tmp.aig; rewrite; dfraig; write tmp.aig"
# abc -c "&r tmp.aig; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &put; write tmp.aig"
# abc -c "read tmp.aig; write tmp.aig"

echo "Calling dot to generate the PDF"
aigtodot tmp.aig | dot -Tpdf -o$1.pdf

open $1.pdf

rm tmp.aig $1.pdf

