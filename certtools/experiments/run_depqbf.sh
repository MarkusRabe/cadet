#!/usr/bin/env bash

solver="depqbf --trace --dep-man=simple --no-lazy-qpup"

while read line; do 
    echo $line 
    filename=${line%.qdimacs}
    filename=${filename##*/}
    gtimeout 120 $solver $line > $filename.qrp
    ../certificate/third_party/qrpcert-1.0.1/qrpcert --simplify $filename.qrp > $filename.depqbf.aag
    ands=`head -n 1 $filename.depqbf.aag | sed -E 's/(aig [0-9]* [0-9]* [0-9]* [0-9]* ([0-9]*))|.*/\2/'`
    echo "Certificate has $ands gates."
done < "random.txt"
