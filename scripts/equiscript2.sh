#!/bin/bash

###################################################################
# The script expects two solvers executables and a qdimacs file   #
# as inputs.                                                      #
#                                                                 #
# Example usage: ./equiscipt.sh ./cadet depqbf5.0 a.qdimacs       #
###################################################################

    echo "Minimizing $3\n" >> dd.log
    
    echo "First solver ..." >> dd.log
    $1 $3 >> dd.log
    r1=$?
    
    echo "Second solver ..." >> dd.log
    $2 $3 >> dd.log
    r2=$?

    if [ "$r1" -ne "$r2" ]; 
    then 
        echo "Discrepancy between solvers $1 and $2"; 
        exit 6
    fi
    exit 0