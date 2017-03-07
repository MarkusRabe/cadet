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

    if [ "$r1" -eq 10 ]; 
    then 
        echo "Second solver ..." >> dd.log
        $2 $3 >> dd.log
        r2=$?
        if [ "$r2" -eq 20 ]; 
        then
            echo "Found the correct discrepancy between solvers $1 and $2";
            exit 6
        fi
    fi
    if [ "$r1" -eq 20 ]; 
    then 
        echo "Second solver ..." >> dd.log
        $2 $3 >> dd.log
        r2=$?
        if [ "$r2" -eq 10 ]; 
        then
            echo "Found the correct discrepancy between solvers $1 and $2";
            exit 6
        fi
    fi
    exit 30