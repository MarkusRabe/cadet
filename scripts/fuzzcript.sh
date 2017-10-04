
###########################################################
# The script expects three inputs. The first two inputs   #
# are tool names and the last one is the number of random #
# files to be generated. The second tool is used as the   #
# reference for determining the number of positive and    #
# negative cases.                                         #
#                                                         #
# Example usage: ./fuzzcript.sh ./cadet depqbf numSamples #
###########################################################

random=$RANDOM
numsat=0
numunsat=0
numerrors=0
echo "Random seed: $random"
for ((i = 1; i <= $3; i++)); do
    echo "--- Iteration #$i ---"
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 200 -v 100 -s 2 -r 0.95) # 20% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 90 -v 30 -s 2 -r 0.9) # 30% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 50 -v 50 -s 2 -r 0.9 --max=4) # 25% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 50 -v 30 -s 2 -r 0.9 --max=6) # 40% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 20 -v 8 -s 2 -r 0.7) # 21% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 20 -v 9 -s 2 -r 0.8) # 40% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 7 -v 4 -s 2 -r 0.6) # 15% SAT
    qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 8 -v 7 -s 2 -r 0.6) # 40% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 12 -v 11 -s 2 --max=2 -r 0.9)
    
    ################ FULL QBF
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py)
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 20 -v 8 -r 0.7)
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 10 -v 5 -r 0.7)
    # cat fuzz$((random+i)).qdimacs | $1 > /dev/null
    # cat fuzz$((random+i)).qdimacs | $2 > /dev/null
    echo "$qdimacs" | $1 > /dev/null
    r1=$?
    echo "$qdimacs" | $2 > /dev/null
    r2=$?
    
    # echo "Return codes are $r1 and $r2"
    
    if [ "$r1" -ne "$r2" ]; 
    then 
        echo "ERROR: discrepancy for file fuzz$((random+i)).qdimacs"; 
        ((numerrors++))
        echo "$qdimacs" > fuzz$((random+i))_"$r1"_"$r2".qdimacs
    fi
    
    if [ "$r2" -eq 10 ]; 
    then 
        ((numsat++))
    else
        ((numunsat++))
    fi
    
done
echo "Reported $numsat SAT results and $numunsat UNSAT results."
echo "Detected $numerrors discrepancies."
exit 0
