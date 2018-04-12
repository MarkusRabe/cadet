#!/bin/bash

# Usage: ./caqecertprove sh <file.qdimacs>
# Launch from this folder; apply only to SAT files

./../cadet --cegar --caqecert --debugging -c skolem.aig $1

# abc -c "read skolem.aig; print_stats; dc2; dc2; print_stats; write skolem.aig;"

abc -c "read skolem.aig; print_stats; dc2; dc2; dc2; print_stats; write skolem.aig;"

./../../../tools/caqe/certcheck $1 skolem.aig > cert.aag

aigtoaig cert.aag cert.aig

# abc -c "&r tmp2.aig; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &put; write tmp2.aig"

cat cert.aig | aigtocnf | lingeling

# picosat 

# rm tmp.aag tmp.aig tmp.dimacs
rm skolem.aig cert.aag cert.aig