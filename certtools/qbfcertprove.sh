#!/bin/bash

./../cadet -c tmp.aag --qbfcert $1

# aigtoaig tmp.aag tmp.aig
# abc -c "read tmp.aig; write tmp.aig; quit"
# aigtoaig tmp.aig tmp.aag

certcheck $1 tmp.aag | lingeling

# picosat 

# rm tmp.aag tmp.aig tmp.dimacs
rm tmp.aag