
###########################################################
# The script expects two inputs. The an executable binary #
# and a number of files to be generated.                  #
#                                                         #
# Example usage: ./fuzzabort.sh ./cadet numSamples        #
###########################################################

random=$RANDOM
numsat=0
numunsat=0
numerrors=0
echo "Random seed: $random"
for ((i = 1; i <= $2; i++)); do
    echo "--- Iteration #$i ---"
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 90 -v 30 -s 2 -r 0.9)
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 50 -v 50 -s 2 -r 0.9 --max=4) # 25% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 50 -v 30 -s 2 -r 0.9 --max=6) # 40% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 20 -v 8 -s 2 -r 0.7) # 21% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 20 -v 9 -s 2 -r 0.8) # 40% SAT
    qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 7 -v 4 -s 2 -r 0.6) # 15% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 7 -v 13 -s 2 -r 0.6) # 100% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 8 -v 7 -s 2 -r 0.6) # 40% SAT
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 12 -v 11 -s 2 --max=2 -r 0.9)
    
    ################ FULL QBF
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 20 -v 8 -r 0.7)
    # qdimacs=$(./debug/qbfuzz-1.1.1/qbfuzz.py --seed=$((random+i)) -c 10 -v 5 -r 0.7)
    # cat fuzz$((random+i)).qdimacs | $1 > /dev/null
    echo "$qdimacs" | $1 > /dev/null
    r1=$?
    echo "Return codes is $r1"
    if [ "$r1" -eq 6 ]; 
    then 
        echo "ERROR: file with return code 6: fuzzabort$((random+i)).qdimacs"; 
        ((numerrors++))
        echo "$qdimacs" > fuzz$((random+i)).qdimacs
    fi
    if [ "$r1" -eq 134 ]; 
    then 
        echo "ERROR: file with return code 11: fuzzabort$((random+i)).qdimacs"; 
        ((numerrors++))
        echo "$qdimacs" > fuzz$((random+i)).qdimacs
    fi
    
    if [ "$r1" -eq 10 ]; 
    then 
        ((numsat++))
    else
        ((numunsat++))
    fi
done
echo "Reported $numsat SAT results and $numunsat UNSAT results."
echo "Detected $numerrors aborts."
exit 0
