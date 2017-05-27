#!/bin/bash

./../cadet -c tmp.aag $1

aigtoaig tmp.aag tmp.aig

# abc -c "read tmp.aig; dc2; write tmp.aig"
# abc -c "read tmp.aig; rewrite; dfraig; write tmp.aig"
abc -c "read tmp.aig; write tmp.aig"

echo "Calling dot to generate the PDF"
aigtodot tmp.aig | dot -Tpdf -o$1.pdf

open $1.pdf

rm tmp.aig tmp.aag $1.pdf