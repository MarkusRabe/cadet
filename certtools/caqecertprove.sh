#!/bin/bash

# Usage: ./caqecertprove sh <file.qdimacs>
# Launch from this folder; apply only to SAT files

./../cadet -c skolem.aig $1

# abc -c "read tmp.aig; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2;  print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; write tmp.aig;"

# some old version
# abc -c "&r tmp.aig; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &put; write tmp.aig"

./../../../tools/caqe/certcheck $1 skolem.aig > cert.aag

aigtoaig cert.aag cert.aig

# abc -c "&r tmp2.aig; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &put; write tmp2.aig"

cat cert.aig | aigtocnf | lingeling

# picosat 

# rm tmp.aag tmp.aig tmp.dimacs
rm skolem.aig cert.aag cert.aig