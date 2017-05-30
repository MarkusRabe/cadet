#!/usr/bin/env bash

while read line; do 
    echo $line
    filename=${line%.qdimacs}
    filename=${filename##*/}
    gtimeout 60 ../cadet -c $filename.aig $line
    abc -q "read $filename.aig; dc2; dc2; dc2; dc2; dc2; write $filename.minimized.aig"
    ands=`head -n 1 $filename.aig | sed -E 's/(aig [0-9]* [0-9]* [0-9]* [0-9]* ([0-9]*))|.*/\2/'`
    echo "Certificate has $ands gates."
    ands=`head -n 1 $filename.minimized.aig | sed -E 's/(aig [0-9]* [0-9]* [0-9]* [0-9]* ([0-9]*))|.*/\2/'`
    echo "Minimized certificate has $ands gates."
done < "random.txt"
