#!/bin/bash

./../cadet -c tmp.aig $1

abc -c "read tmp.aig; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2;  print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; write tmp.aig;"

# abc -c "&r tmp.aig; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &put; write tmp.aig"

./../../tools/caqe/certcheck $1 tmp.aig > tmp.aag

aigtoaig tmp.aag tmp2.aig

abc -c "&r tmp2.aig; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &put; write tmp2.aig"

cat tmp2.aig | aigtocnf | lingeling

# picosat 

# rm tmp.aag tmp.aig tmp.dimacs
rm tmp.aig tmp.aag tmp2.aig