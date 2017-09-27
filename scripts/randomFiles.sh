#!/bin/bash

# Usage: randomFiles.sh dir number

ls -1 $1 | python -c "import sys; import random; print('$1' + '$1'.join(random.sample(sys.stdin.readlines(), int(sys.argv[1]))).rstrip())" $2
