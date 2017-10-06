#!/usr/bin/env python

import sys, os, re, argparse, random, signal, multiprocessing, Queue, threading
import numpy as np
import matplotlib.pyplot as plt

from reporting import log, log_progress, cyan, red, green, yellow
from command import call
        
if __name__ == "__main__":
    
    assert(len(sys.argv) == 2);
    
    return_value1, output1, error1 = call("./cadet -v 1 " + sys.argv[1], 10)
    return_value2, output2, error2 = call("./cadet -v 1 --qbce " + sys.argv[1], 10)
    
    if return_value1 == 42 and return_value2 == 42:
        matches1 = re.findall("Deterministic vars on dlvl 0: (\d+)", output1, flags=0)
        matches2 = re.findall("Deterministic vars on dlvl 0: (\d+)", output2, flags=0)
    
        assert(len(matches1) == 1)
        assert(len(matches2) == 1)
    
        if int(matches1[0]) < int(matches2[0]):
            sys.exit(1)
        else:
            sys.exit(2)
    
    sys.exit(0)
    
