#!/bin/bash

./../cadet --sat_by_qbf -e tmp.aag $1

aigtoaig tmp.aag tmp.aig
# abc -c "read tmp.aig; write tmp.aig"
abc -c "read tmp.aig; print_stats; dc2; dc2; dc2; print_stats; write tmp.aig"
aigtoaig tmp.aig tmp.aag


echo "Calling dot to generate the PDF"
aigtodot tmp.aag | dot -Tpdf -o$1.pdf

open $1.pdf

rm tmp.aag tmp.aig $1.pdf

