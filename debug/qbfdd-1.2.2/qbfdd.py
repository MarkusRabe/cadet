#! /usr/bin/env python3
#
# QBFDD is a delta debugger for QBF (Quantified Boolean Formulas) solvers.
# Copyright (c) 2009, 2010, 2011, Aina Niemetz
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""
A delta debugger for QBF files in QDIMACS format. 
"""
import re
import os
import sys
import math
import time
import copy
import textwrap
from subprocess import Popen, PIPE
from optparse import OptionParser, IndentedHelpFormatter

__version__  = "1.2.2"
__author__ = "Aina Niemetz <aina.niemetz at gmail.com>"


class QBFDDError(Exception):
    """Raised, if any error during ddmin occurs."""
    
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return("[ERROR] " + self.msg)


class QBFDD:
    """
    The QBF Delta Debugger.

    QBFDD is a delta debugger for QBF files in QDIMACS format. It serves as an 
    input minimizer for QBF solvers failing on some given input by removing as 
    many clauses and literals from that input as possible without making the 
    solver pass on the minimized input.

    The minimized input generated is QDIMACS standard 1.1 compliant by default
    (see http://www.qbflib.org/qdimacs.html#input). Standard compliance can
    optionally be disabled.
    
    Based on 2 basic minimization algorithms, currently 6 different so called
    'modi' are supported:
        - DDMIN   : A. Zeller's ddmin as in [1]
        - SDDMIN  : the 'simple' DDMIN, again A. Zeller's ddmin as in [2]
        - IDDMIN  : inverse ddmin
        - ISDDMIN : inverse sddmin
        - OBO     : one by one
        - QOBO    : quick one by one

    DDMIN and SDDMIN are based on A. Zeller's delta debugging algorithms 
    provided in [1] and [2]. IDDMin and ISDDMIN are the 'inverse' variants
    of both.
    OBO and QOBO are based on a linear approach: literally 'one by one'. The
    main difference between them two is, that OBO restarts after a successful
    minimization and QOBO doesn't (therefore the 'quick' in QOBO).

    Additionally, if enabled, so called quantifier manipulations - or shifts -
    are performed on the minimized input in order to maybe accomplish even
    further minimizations (disabled by default).

    Further, it is possible to define a so called minimization granularity, 
    that is, either of both steps - removing clauses and removing literals -
    may be skipped.

    Some words about semantics of terms used here:
    A test run may FAIL or PASS on given input. We are looking for test runs
    that FAIL (as this is the original behaviour of the solver on the originally
    given input). 
    If a test run FAILs, the respective minimization step was SUCCESSFUL.
    If a test run PASSes, it wasn't.

    By default, QBFDD uses stdout and stderr of the given executable in order
    to determine, if a test run failed or not (if the behaviour of the solver
    is the same as in the original test run or not). 
    This can be optionally disabled.

    Further, it is possible to define timeouts for test runs (disabled by
    default).

    Note, that QBFDD uses colored output for better readability. This can
    be disabled optionally.

    [1] A. Zeller, R. Hildebrandt: Simplifying failure-inducing input, 
        ISSTA 2000
    [2] A. Zeller: Why programs fail, ISBN 3-89864-279-8, dpunkt Verlag,
        1. ed., 2006
    """ 
    PASSED = 0
    FAILED = 1
    UNRESOLVED = 2

    DDMIN = "ddmin"
    SDDMIN = "sddmin"
    IDDMIN = "iddmin"
    ISDDMIN = "isddmin"
    OBO = "obo"
    QOBO = "qobo"
    # maybe these would be a nice-to-have in the future:
    #ROBO = "robo"
    #QROBO = "qrobo"

    BOTH = "b"
    CONLY = "c"
    LONLY = "l"

    BASH_STD = "\033[0;39m"
    BASH_GREEN = "\033[1;32m"
    BASH_RED = "\033[0;31m"
    BASH_YELLOW = "\033[0;33m"
    BASH_BLUE = "\033[1;34m"
    BASH_GRAY = "\033[1;30m"


    def __init__(self, infile, cmd, outfile=None, tmpfile=None, 
                 failed=None, passed=None, mode=DDMIN, gran=BOTH, 
                 verbose=0, compliant=True, shift=False, skip=False, 
                 timeout=0, use_bash_colors=True):
        
        self.infile = infile

        if tmpfile == None:
            self.tmpfile = "/tmp/tmp-" + str(os.getpid()) + ".qdimacs"
        else:
            self.tmpfile = tmpfile

        if outfile == None:  # use infile"_reduced".ext
            ext = ''
            self.outfile = ""
            pattern = re.compile("\.")
            infile = self.infile.strip().split("/")[-1]       # drop path
            infile_path_items = pattern.split(infile.strip())
            if len(infile_path_items) > 1:
                ext = "_reduced." + infile_path_items.pop(-1)
            else:
                ext = "_reduced"
            for item in infile_path_items:
                self.outfile += item
            self.outfile += ext
        else:
            self.outfile = outfile

        self.cmd = cmd
        self.repr = "qbfdd.py " + os.path.realpath(self.infile) + " " + \
                    os.path.realpath(self.cmd)

        self.failed = None
        if failed != None:
            try:
                self.failed = int(failed)
                self.repr += " -f " + str(self.failed)
            except ValueError as err:
                raise QBFDDError("invalid return value: {0!s}".format(failed))
        self.passed = None
        if passed != None:
            try:
                self.passed = int(passed)
                self.repr += " -p " + str(self.passed)
            except ValueError as err:
                raise QBFDDError("invalid return value: {0!s}".format(passed))
        
        if mode not in [self.DDMIN, self.SDDMIN, self.IDDMIN, self.ISDDMIN, 
                        self.OBO, self.QOBO]:
            raise QBFDDError("invalid mode: {0!s}".format(mode))
        self.mode = mode
        self.repr += " -m " + mode

        if gran not in [self.BOTH, self.CONLY, self.LONLY]:
            raise QBFDDError("invalid granularity: {0!s}".format(gran))
        self.gran = gran
        self.repr += " -g " + gran

        self.verbose = verbose
        self.compliant = compliant
        
        self.shift = shift
        if self.shift:
            self.quants_cache = Cache()

        self.skip = skip
        try: 
            self.timeout = int(timeout)
            if self.timeout < 0:
                raise ValueError()
            elif self.timeout > 0:
                self.repr += " -t " + str(self.timeout)
        except ValueError as err:
            raise QBFDDError("invalid timeout: {0!s}".format(timeout))
        self.n_timeouts = 0

        opts = ''
        if not self.compliant:
            opts += "q"
        if self.shift:
            opts += "s"
        if self.skip:
            opts += "S"

        if use_bash_colors:
            self.green = self.BASH_GREEN
            self.red = self.BASH_RED
            self.yellow = self.BASH_YELLOW
            self.blue = self.BASH_BLUE
            self.gray = self.BASH_GRAY
            self.std = self.BASH_STD
        else:  # do not clutter e.g. redirected output
            self.green = self.red = self.yellow = self.gray = self.std = ''
            opts += "c"

        if opts != '':
            self.repr += " -" + opts

        self.num_vars = 0     # used for better readability
        self.ref_count = [0]
        self.quantsets = []
        self.clauses = []
        
        self.std_out = ""
        self.std_err = ""
        self.exit_code = 0
        self.test_runs = 0
        self.successful = False

    
    def dd(self):
        """
        Initiate the delta debugging procedure, original input is minimized
        successively (according to the previously chosen mode) until a 
        1-minimal failure inducing configuration is found;
        result is written to output file in QDIMACS format.
        """
        start = time.time()
        parser = QBFParser()
        comments = []
        rounds = 0
        rounds_ = 0

        if self.verbose:
            start_parse = time.time()
            print("\nversion: {0}".format(__version__))
            print("parsing input file: {0}".format(self.infile))

        try:
            (self.num_vars, self.ref_count, self.quantsets, self.clauses) = \
                parser.parse_file(self.infile)
            num_quantsets = len(self.quantsets)
            if self.compliant and \
               len(self.quantsets) == 1 and self.quantsets[-1][0] == 'a':
                raise QBFDDError("it's impossible to fullfill QDIMACS " \
                        "compliance if only one single\n        universal "\
                        "quantset is given, retry with -q enabled")
        except QBFParseError as err:
            raise QBFDDError(err.msg)
        except IOError as err:
            raise QBFDDError(err.strerror + ": " + args[0])

        # statistics
        num_vars_orig = num_vars_prev = self.num_vars
        num_clauses_orig = num_clauses_prev = len(self.clauses)
        num_lits_orig = 0
        for count in self.ref_count:
            num_lits_orig += count
        num_lits_prev = num_lits_orig

        if self.verbose:
            print("parsed: {0} clause(s), {1} variable(s), {2} literal(s)\t\t" \
                  "{3}{4:7.2f}ms{5}".format(
                      num_clauses_orig, num_vars_orig, num_lits_orig, self.gray,
                      (time.time() - start_parse) * 1000, self.std))

        # write file for initial test run
        if self.verbose > 1:
            start_write = time.time()
            print("writing original configuration to output file...", end='')
            sys.stdout.flush()

        self._write_file(self.tmpfile, 
                         self.num_vars, self.quantsets, self.clauses)
        
        if self.verbose > 1:
            print("\t\t{0}{1:7.2f}ms{2}".format(
                      self.gray, (time.time() - start_write) * 1000, self.std))
            print("starting initial test run... ", end='')
            sys.stdout.flush()
            start_test = time.time()

        # initial test run (not counted)
        self._test_initial()

        if self.verbose > 1:
            print("done\t\t\t\t{0}{1:7.2f}ms{2}".format(
                      self.gray, (time.time() - start_test) * 1000, self.std))

        if self.exit_code < 0:  # process killed by signal
            if self.failed != None:
                raise QBFDDError("initial test run killed unexpectedly")
        else:                   # normal termination
            if self.failed != None and self.failed != self.exit_code:
                raise QBFDDError("given input is no failing set")
            if self.failed == None:
                self.failed = self.exit_code


        # minimization procedure (gran=BOTH)
        #  
        #  |
        #  v   rounds++   |--------------------------|  done
        #  |------------->| reduce number of clauses |---------------
        #  |              |--------------------------|              |
        #  |                          |                             |
        #  |                          | !done or                    |
        #  |                          | self.shift and rounds_ > 0  |
        #  |                          v                             |
        #  |              |--------------------------|              |
        #  |<-------------|   minimize each clause   |              |
        #  |   !done      |--------------------------|              |
        #  |                          |                             |
        #  |                          | done and self.shift         |
        #  |                          v                             |
        #  |   rounds_++  |--------------------------|              |
        #  |<-------------| quantifier manipulations |              |
        #      !done      |--------------------------|              |
        #                             |                             |
        #                             | done                        |
        #                             |                             |
        #                             v<-----------------------------  
        while 1:
            done = False
            # rounds: reduce number of clauses, minimize clauses
            while not done:
                rounds += 1
                if self.gran != self.LONLY:
                    # reduce number of clauses
                    if self.verbose:
                        start_red = time.time()
                        print("\n{0} clause(s), {1} variable(s), {2} literal" \
                              "(s) in round {3}".format(num_clauses_prev, 
                                                        num_vars_prev, 
                                                        num_lits_prev, rounds))
                        if self.verbose > 1:
                            print("reducing number of clauses")
                        else:
                            print("reducing number of clauses", end='')
                            sys.stdout.flush()

                    if self.mode == self.DDMIN:
                        (successful, self.clauses) = self._ddmin(self.clauses)
                    elif self.mode == self.SDDMIN:
                        (successful, self.clauses) = \
                            self._ddmin(self.clauses, simple=True)
                    elif self.mode == self.IDDMIN:
                        (successful, self.clauses) = \
                            self._ddmin(self.clauses, inverse=True)
                    elif self.mode == self.ISDDMIN:
                        (successful, self.clauses) = \
                            self._ddmin(self.clauses, simple=True, inverse=True)
                    elif self.mode == self.OBO:
                        (successful, self.clauses) = self._obo(self.clauses)
                    elif self.mode == self.QOBO:
                        (successful, self.clauses) = \
                            self._obo(self.clauses, quick=True)
                    else:
                        # this may never happen (handled in __init__ already)
                        raise QBFDDError("invalid mode: {0}".format(self.mode))

                    if self.verbose:
                        if self.verbose > 1:
                            print("reducing number of clauses", end='')
                            sys.stdout.flush()

                        if not successful:
                            print(": {0}not successful{1}\t\t\t{2}{3:7.2f}s" \
                                  "{4}".format(self.red, self.std, self.gray, 
                                               time.time() - start_red, 
                                               self.std))
                        else:
                            print(": {0}successful{1}\t\t\t\t{2}{3:7.2f}s"\
                                  "{4}".format(self.green, self.std, self.gray, 
                                               time.time() - start_red, 
                                               self.std))

                    # last step unsuccessful in any round except the first and
                    # quantifier manipulations either disabled or unsuccessful
                    # -> no more minimization possible
                    if (not successful and rounds > 1 and rounds_ == 0) or \
                       (not successful and self.gran == self.CONLY):
                        rounds -= 1  # this round doesn't count for statistics
                        break


                if self.gran != self.CONLY:
                    # minimize clauses
                    done = True
                    if self.verbose:
                        num_lits = 0
                        for count in self.ref_count:
                            num_lits += count
                        print("-{0} clause(s), -{1} variable(s), -{2} literal"\
                              "(s) after reduction".format(
                                  num_clauses_prev - len(self.clauses), 
                                  num_vars_prev - self.num_vars, 
                                  num_lits_prev - num_lits))
                        num_clauses_prev = len(self.clauses)
                        num_vars_prev = self.num_vars
                        num_lits_prev = num_lits
                        start_min = time.time()
                        if self.verbose > 1:
                            print("\nminimizing clauses")
                        else:
                            print("minimizing clauses", end='')
                            sys.stdout.flush()

                    for i in range(0,len(self.clauses)):
                        clause = self.clauses[i][:]

                        if self.verbose > 1:
                            print("\nclause: ", end='')
                            sys.stdout.flush()
                            print(*clause)

                        if self.mode == self.DDMIN:
                            (successful, self.clauses[i]) = \
                                self._ddmin(clause, i)
                        elif self.mode == self.SDDMIN:
                            (successful, self.clauses[i]) = \
                                self._ddmin(clause, i, simple=True)
                        elif self.mode == self.IDDMIN:
                            (successful, self.clauses[i]) = \
                                self._ddmin(clause, i, inverse=True)
                        elif self.mode == self.ISDDMIN:
                            (successful, self.clauses[i]) = \
                                self._ddmin(clause, i, simple=True, 
                                            inverse=True)
                        elif self.mode == self.OBO:
                            (successful, self.clauses[i]) = self._obo(clause, i)
                        elif self.mode == self.QOBO:
                            (successful, self.clauses[i]) = \
                                self._obo(clause, i, quick=True)
                        else:
                            # this may never happen 
                            # (handled in __init__ already)
                            raise QBFDDError(
                                    "invalid mode: {0}".format(self.mode))
                        
                        # any of the minimization steps was successful: continue
                        # all of them were not successful: done
                        if successful:
                            done = False
               
                    if self.verbose:
                        if self.verbose > 1:
                            print("minimizing clauses", end='')
                            sys.stdout.flush()
                        if done:
                            print(": {0}not successful{1}\t\t\t\t{2}{3:7.2f}s" \
                                  "{4}".format(self.red, self.std, self.gray, 
                                               time.time() - start_min, 
                                               self.std))
                        else:
                            print(": {0}successful{1}\t\t\t\t\t{2}{3:7.2f}s" \
                                  "{4}".format(self.green, self.std, self.gray, 
                                               time.time() - start_min, 
                                               self.std))
                        num_lits = 0
                        for count in self.ref_count:
                            num_lits += count
                        assert(num_clauses_prev == len(self.clauses))
                        print("-{0} variable(s), -{1} literal(s) after "
                              "minimization step".format(
                                  num_vars_prev - self.num_vars, 
                                  num_lits_prev - num_lits))
                        if self.n_timeouts > 0:
                            print("{0}warning!{1} {2} test runs aborted "\
                                  "(timeout)".format(self.blue, self.std, 
                                                     self.n_timeouts))
                            self.n_timeouts = 0  # reset
                        print("{0}-{1} clause(s), -{2} variable(s), -{3} " \
                              "literal(s) after round {4}{5}".format(
                                  self.yellow, 
                                  num_clauses_orig - len(self.clauses),
                                  num_vars_orig - self.num_vars, 
                                  num_lits_orig - num_lits, rounds, self.std))
                        num_clauses_prev = len(self.clauses)      
                        num_vars_prev = self.num_vars
                        num_lits_prev = num_lits
                    # end for
            # end while
            if not self.shift: 
                break
            elif not len(self.quantsets) > 1 and self.quantsets[0][0] == 'e':
                if self.verbose:
                    print("only one quantset left, skipping quantifier "\
                          "manipulations")
                break
            else:
                # quantifier manipulations
                if self.verbose:
                    start_shift = time.time()
                    if self.verbose > 1:
                        print("\nmanipulating quantifiers")
                    else:
                        print("manipulating quantifiers", end='')

                successful = self._shift()

                if self.verbose:
                    if self.verbose > 1:
                        print("manipulating quantifiers", end='')
                        sys.stdout.flush()
                    if successful:
                        print(": {0}successful{1}\t\t\t{2}{3:7.2f}s{4}".format(
                                  self.green, self.std, self.gray, 
                                  time.time() - start_shift, self.std))
                    else:
                        print(": {0}not successful{1}\t\t\t{2}{3:7.2f}s" \
                              "{4}".format(self.red, self.std, self.gray,
                                           time.time() - start_shift, self.std))
                if not successful:
                    break
                else:  # quantifier manipulations have been successful
                    rounds_ += 1
        # end while

        # write result
        if self.compliant:
            if self.verbose > 1:
                start_upd = time.time()
                print("\nupdating in order to be QDIMACS compliant...", 
                      end='')
                sys.stdout.flush()

            (self.ref_count, self.quantsets, self.clauses) = \
                  self._update(self.ref_count, self.quantsets, self.clauses)
            self.num_vars = len(self.ref_count) - self.ref_count.count(0)
            assert(self.num_vars > 0)
            assert(self.quantsets[-1][0] != 'a')
        
            if self.verbose > 1:
                print("\t\t\t{0}{1:7.2f}ms{2}".format(
                      self.gray, (time.time() - start_upd) * 1000, 
                      self.std))

        time_elapsed = time.time() - start
        num_lits = 0
        for count in self.ref_count:
            num_lits += count
        comments.append("{0} by qbfdd.py,v {1}".format( 
                        time.strftime("%Y-%m-%d %H:%M:%S"), __version__))
        comments.append(self.repr)
        comments.append("")
        comments.append("mode: " + self.mode)
        comments.append("rounds: {0}".format(rounds))
        if self.shift:
            comments.append("quants manipulated: {0}".format(rounds_))
        comments.append("test runs: {0}".format(self.test_runs))
        comments.append("time elapsed: {0:5.2f}s".format(time_elapsed))
        comments.append("total: clauses  : -{0} ({1:.2%})".format(
                            num_clauses_orig - len(self.clauses), 
                            1 - len(self.clauses)/num_clauses_orig))
        comments.append("       variables: -{0} ({1:.2%})".format(
                            num_vars_orig - self.num_vars, 
                            1 - self.num_vars/num_vars_orig))
        comments.append("       literals : -{0} ({1:.2%})".format(
                            num_lits_orig - num_lits, 
                            1 - num_lits/num_lits_orig))
        comments.append("")

        if self.verbose > 1:
            start_write = time.time()
            print("writing new configuration to output file...", end='')
            sys.stdout.flush()

        self._write_file(self.outfile, 
                         self.num_vars, self.quantsets, self.clauses, comments)

        try:
            os.remove(self.tmpfile)
        except (OSError, ValueError) as err:
            if self.verbose > 1:
                print()
            raise QBFDDError(err.strerror + ": " + command[0])

        if self.verbose > 1:
            print("\t\t\t{0}{1:7.2f}ms{2}".format(
                      self.gray, (time.time() - start_write) * 1000, 
                      self.std))

        if self.verbose:
            if not self.successful:
                print("\ndone: {0}not successful{1}".format(self.red, self.std))
            else:
                print("done")    
            print("\nrounds: {0}".format(rounds))
            if self.shift:
                print("quants manipulated: {0}".format(rounds_))
            print("test runs: {0}".format(self.test_runs))
            print("time elapsed: {0:7.2f}s".format(time_elapsed))
            print("total: clauses  : -{0} (-{1:.2%})".format(
                      num_clauses_orig - len(self.clauses), 
                      1 - len(self.clauses)/num_clauses_orig))
            print("       variables: -{0} (-{1:.2%})".format(
                      num_vars_orig - self.num_vars, 
                      1 - self.num_vars/num_vars_orig))
            print("       literals : -{0} (-{1:.2%})".format( 
                      num_lits_orig - num_lits, 1 - num_lits/num_lits_orig))


    def _ddmin(self, superset, index=0, simple=False, inverse=False):
        """
        _ddmin(superset: [...] or [[],[],...],
               index   : int,
               simple  : bool,
               inverse : bool)

        Minimize given input according to A. Zeller's ddmin algorithms,
        where 4 different modi are possible:
            - ddmin (simple=False, inverse=False) [1]
            - iddmin (simple=False, inverse=True)
            - sddmin (simple=True, inverse=False) [2]
            - isddmin (simple=True, inverse=True)

        Return a 1-minimal failure-inducing subset of given superset and True
        if the minimization procedure was successful and False otherwise.
        
        [1] A. Zeller, R. Hildebrandt: Simplifying failure-inducing input, 
            ISSTA 2000
        [2] A. Zeller: Why programs fail, ISBN 3-89864-279-8, dpunkt Verlag,
            1. ed., 2006
        """
        start = time.time()
        superset_orig = superset[:] 
        
        if superset in self.clauses:  # set of literals -> single clause
            single = True
        else:                         # set of clauses
            single = False

        results = Cache()
        successful = False

        if inverse:
            n = len(superset)
        else:
            n = 2

        if self.verbose > 1 and len(superset) < 2:
            if single:
                print("only one literal left, skipping")
            else:
                print("only one clause left, skipping")

        while len(superset) >= 2:
            subsets = self._split(superset, n)
            assert(len(subsets) == n)
            has_failed = False

            if not simple:  # ddmin, iddmin: test subsets and complements
                to_complement = False
            else:           # sddmin, isddmin: test complements only, no subsets
                to_complement = True

            while 1:
                if self.verbose > 1 and not simple:
                    if not to_complement:
                        # test subsets (first step)
                        print("testing subsets...")
                    else:
                        # test complements (second step)
                        print("testing complements...")

                for i in range(len(subsets)):
                    if single:
                        (count, quants, clause_s) = \
                            self._minimize(superset, subsets, i, to_complement)
                    else:    
                        (count, quants, clause_s) = \
                            self._reduce(subsets, i, to_complement)

                    index_list = self._get_indices(clause_s, superset_orig)

                    # check if this set of clauses has already been tested
                    if results.look_up(index_list):
                        continue
                
                    if single:             
                        clause = clause_s[:]
                        assert(clause != [])
                        clause_s = self.clauses[:]
                        clause_s[index] = clause[:] 

                    if self.compliant:
                        # be QDIMACS compliant
                        if len(quants) == 1 and quants[-1][0] == 'a':
                            if self.verbose > 1:
                                print("only one universal quantset left, " \
                                      "skipping test run")
                            continue

                        if self.verbose > 1:
                            start_upd = time.time()
                            print("updating in order to be QDIMACS "\
                                  "compliant...", end='')
                            sys.stdout.flush()

                        (count_upd, quants_upd, clause_s_upd) = \
                            self._update(count, quants, clause_s)
                        if self.verbose > 1:
                            print("\t\t\t{0}{1:7.2f}ms{2}".format(
                                  self.gray, (time.time() - start_upd) * 1000, 
                                  self.std))
                    else:
                        count_upd = count
                        quants_upd = quants
                        clause_s_upd = clause_s
                    
                    if (len(count_upd) - 1) == 0:
                        if self.verbose > 1:
                            print("empty set, skipping test run")
                    else:
                        # write file for test run
                        if self.verbose > 1:
                            start_write = time.time()
                            print("writing new configuration to output file...",
                                  end='')
                            sys.stdout.flush()

                        self._write_file(self.tmpfile, len(count_upd) - 1, 
                                         quants_upd, clause_s_upd)
                    
                        if self.verbose > 1:
                            print("\t\t\t{0}{1:7.2f}ms{2}".format(
                                  self.gray, (time.time() - start_write) * 1000,
                                  self.std))
                            start_test = time.time()

                        # test run
                        test_result = self._test()

                        if self.verbose > 1:
                            print("test run: {0:4d}\t".format(self.test_runs), 
                                  end='')
                            print("granularity: {0:3d} ".format(n), end='') 
                            sys.stdout.flush()
                    
                        results.add(index_list, test_result)
                    
                        if test_result == self.FAILED:
                            superset = clause_s[:]
                            if single:             
                                superset = clause_s[index][:]
                            # keep the original (not updated) sets
                            self.quantsets = quants[:]
                            self.ref_count = count[:]
                            if self.compliant:
                                self.num_vars = len(self.ref_count) - \
                                                self.ref_count.count(0)
                            if inverse:
                                n = len(superset)
                            else:
                                if not to_complement:
                                    n = 2
                                else:
                                    n = max(n-1, 2)

                            has_failed = True
                            successful = True
                            # save successful config 
                            self._write_file(self.outfile, len(count_upd) - 1, 
                                             quants_upd, clause_s_upd)

                            if self.verbose > 1:
                                print("\t{0}successful{1}\t\t{2}{3:7.2f}ms" \
                                      "{4}".format(
                                          self.green, self.std, self.gray, 
                                          (time.time() - start_test) * 1000,
                                          self.std))
                            to_complement = True  # force break of outer while
                            break
                        elif self.verbose > 1:
                            print("\t{0}not successful{1}\t\t{2}{3:7.2f}ms" \
                                  "{4}".format(self.red, self.std, self.gray, 
                                              (time.time() - start_test) * 1000,
                                              self.std))
                    # end for
                if not to_complement:
                    to_complement = True  # proceed with second step
                else:
                    break                 # done
            # end while
            if not has_failed:
                if inverse:
                    if n == 2:
                        break
                    m = len(superset) // n
                    m += 1
                    n = max(len(superset) // m, 2)
                else:
                    if n == len(superset):
                        break;
                    n = min(n*2, len(superset))
        # end while
        return (successful, superset)


    def _obo(self, superset, index=0, quick=False):
        """
        _obo(superset: [...] or [[],[],...],
             index   : int,
             quick   : bool)
        
        Minimize given input in a linear manner (one by one), where 2 different
        modi are possible:
            - obo (quick=False)
            - qobo (quick=True)
        
        Return a 1-minimal failure-inducing subset of given superset and True
        if the minimization procedure was successful, False otherwise.

        "one by one" is meant literally in this case: Given superset is split
        into len(superset) subsets, then subsets are eliminated one by one from 
        the first to the last. The main difference between OBO and QOBO is the
        way how to proceed after eliminating a subset: OBO restarts from the 
        very beginning (subsets[0]), QOBO proceeds with the current index.
        """
        # maybe resp. reverse modi ROBO and QROBO would be a nice-to-have
        # in the future?
        start = time.time()
        superset_orig = superset[:] 

        if superset in self.clauses:   # set of literals -> single clause
            single = True
        else:                          # set of clauses
            single = False

        results = Cache()
        successful = False
        
        if self.verbose > 1 and len(superset) < 2:
            if single:
                print("only one literal left, skipping")
            else:
                print("only one clause left, skipping")


        while len(superset) >= 2:
            subsets = self._split(superset, len(superset))
            assert(len(subsets) == len(superset))
            has_failed = False
            
            i = 0
            while 1:
                if i >= len(subsets):
                    break
                if single:
                    (count, quants, clause_s) = \
                            self._minimize(superset, subsets, i, 
                                            to_complement=True)
                else:
                    (count, quants, clause_s) = \
                            self._reduce(subsets, i, to_complement=True)
                index_list = self._get_indices(clause_s, superset_orig)
                # check if this set of clauses has already been tested
                if results.look_up(index_list):
                    i += 1
                    continue
                
                if single:
                    clause = clause_s[:]
                    assert(clause != [])
                    clause_s = self.clauses[:]
                    clause_s[index] = clause[:] 

                if self.compliant:
                    # be QDIMACS compliant
                    if len(quants) == 1 and quants[-1][0] == 'a':
                        if self.verbose > 1:
                            print("only one universal quantset left, " \
                                  "skipping test run")
                        i += 1
                        continue

                    if self.verbose > 1:
                        start_upd = time.time()
                        print("updating in order to be QDIMACS compliant...", 
                              end='')
                        sys.stdout.flush()

                    (count_upd, quants_upd, clause_s_upd) = \
                        self._update(count, quants, clause_s)
                    
                    if self.verbose > 1:
                        print("\t\t\t{0}{1:7.2f}ms{2}".format(
                                  self.gray, (time.time() - start_upd) * 1000, 
                                  self.std))
                else:
                    count_upd = count
                    quants_upd = quants
                    clause_s_upd = clause_s
                
                # write file for test run
                if (len(count_upd) - 1) == 0:
                    if self.verbose > 1:
                        print("empty set, skipping test run")
                else:
                    if self.verbose > 1:
                        start_write = time.time()
                        print("writing new configuration to output file...", 
                              end='')
                        sys.stdout.flush()

                    self._write_file(self.tmpfile, len(count_upd) - 1, 
                                     quants_upd, clause_s_upd)
                    
                    if self.verbose > 1:
                        print("\t\t\t{0}{1:7.2f}ms{2}".format(
                                 self.gray, (time.time() - start_write) * 1000, 
                                 self.std))
                        start_test = time.time()

                    # test run
                    test_result = self._test()

                    if self.verbose > 1:
                        print("test run: {0:4d}\t".format(self.test_runs), 
                              end='')
                        sys.stdout.flush()
                    
                    results.add(index_list, test_result)

                    if test_result == self.FAILED:
                        subsets.pop(i)
                        if i < len(subsets) - 1:  # this was not the last subset
                            i -= 1
                        superset = clause_s[:]
                        if single:             
                            superset = clause_s[index][:]
                        self.quantsets = quants[:]
                        self.ref_count = count[:]
                        if self.compliant:
                            self.num_vars = \
                                len(self.ref_count) - self.ref_count.count(0) 
                        has_failed = True
                        successful = True
                        # save successful config 
                        self._write_file(self.outfile, len(count_upd) - 1, 
                                         quants_upd, clause_s_upd)

                        if self.verbose > 1:
                            print("\t{0}successful{1}\t\t\t\t{2}{3:7.2f}ms" \
                                  "{4}".format(
                                      self.green, self.std, self.gray, 
                                      (time.time() - start_test) * 1000, 
                                      self.std))
                        if not quick:  # restart
                            break
                    elif self.verbose > 1:
                        print("\t{0}not successful{1}\t\t\t\t{2}{3:7.2f}ms" \
                              "{4}".format(self.red, self.std, self.gray, 
                                           (time.time() - start_test) * 1000, 
                                           self.std))
                i += 1
                # end while
            if not has_failed:
                break
            # end while
        return (successful, superset)


    def _test_initial(self):
        """
        Initial test run. 
        Determine exit code and behaviour of solver (given by command) on 
        original input, abort if a given timeout is exceeded;
        raises QBFDDError.
        
        Note: Original input has to be written to self.output up front.
        """
        pattern = re.compile("\s+")
        command = pattern.split(self.cmd.strip())
        command.append(self.tmpfile)
        start = time.time()
        
        try:
            test_run = Popen(command, stdout=PIPE, stderr=PIPE)
        except (OSError, ValueError) as err:
            if self.verbose > 1:
                print()
            raise QBFDDError(err.strerror + ": " + command[0])
        
        if self.timeout > 0:
            while test_run.poll() == None:
                if (time.time() - start) > self.timeout:
                    test_run.kill()
                    if self.verbose > 1:
                        print()
                    raise QBFDDError("initial test run: timeout")
                time.sleep(0.1)
        # else timeout functionality disabled

        self.std_out, self.std_err = test_run.communicate()
        self.exit_code = test_run.returncode

   
    def _test(self):
        """
        Test run.
        Determine exit code and behaviour of solver (given by command) on 
        minimized input, abort test run and treat as unsuccessful if a given
        timeout is exceeded;
        return PASSED if solver passed (minimization not successful), 
               FAILED if solver failed (minimization successful) and
               UNRESOLVED if we can't tell;
        raises QBFDDError.

        Note: Minimized input has to be written to self.tmpfile up front.
        """
        self.test_runs += 1

        pattern = re.compile("\s+")
        command = pattern.split(self.cmd.strip())
        command.append(self.tmpfile)
        start = time.time()

        try:
            test_run = Popen(command, stdout=PIPE, stderr=PIPE)
        except (OSError, ValueError) as err:
            if self.verbose > 1:
                print()
            raise QBFDDError(err.strerror + ": " + command[0])

        if self.timeout > 0:
            while test_run.poll() == None:
                if (time.time() - start) > self.timeout:
                    test_run.kill()
                    if self.verbose:
                        self.n_timeouts += 1
                        if self.verbose > 1:
                            print("{0}warning!{1} test run {2} aborted " \
                                  "(timeout)".format(
                                      self.blue, self.std, self.test_runs))
                    # we are not looking for test runs aborted due to a timeout
                    return self.PASSED
                time.sleep(0.1)
        # else timeout functionality disabled

        out, err = test_run.communicate()
        ret = test_run.returncode

        # external process termination (assertion errors, segfaults, ...)
        if self.failed == None:
            assert(self.exit_code < 0)
            if ret == self.exit_code:
                if self.skip or (out == self.std_out and err == self.std_err):
                    self.successful = True
                    return self.FAILED
                else:
                    return self.PASSED
            else:
                # any case except the one above counts as 'passed', even if an
                # exit code for passed runs is given but not met (irrelevant)
                return self.PASSED

        # no external process termination, no ret val for passed test runs
        if self.failed != None and self.passed == None:
            if ret >= 0:
                if ret == self.failed:
                    self.successful = True
                    return self.FAILED
                return self.PASSED
            else:
                print("\n============Internal Error. Last process returned code " + str(ret))
                print("Last output: " + str(out))
                print("Last err: " + str(err))
                print("\n============")
                print("Tempfile is here: " + self.tmpfile)
                print("Command was: " + str(command))
                raise QBFDDError("test run killed unexpectedly")
        
        # no external process termination, ret val for both passed and failed
        assert(self.failed != None and self.passed != None)
        if ret >= 0:
            if ret == self.passed:
                return self.PASSED
            elif ret == self.failed:
                self.successful = True
                return self.FAILED
        
        return self.UNRESOLVED


    def _write_file(self, filename, n_vars, quantsets, clauses, comments=None):
        """
        _write_file(filename    : string,
                    n_vars      : int,
                    quantsets   : [[(e|a), [int, ...]], ...], 
                    clauses     : [[int, ...], ...],
                    comments    : [string, ...])

        Write given configuration to given file;
        raises QBFDDError.
        """
        try:
            with open(filename, 'w') as outfile:
                if comments:
                    for comment in comments:
                        outfile.write("c " + str(comment) + "\n")
                outfile.write("p cnf {0} {1}\n".format(n_vars, len(clauses)))
                for quantset in quantsets:
                    outfile.write("{0} ".format(quantset[0]))
                    for literal in quantset[1]:
                        outfile.write("{0} ".format(literal))
                    outfile.write("0\n")

                for clause in clauses:
                    for literal in clause:
                        outfile.write(str(literal) + " ")
                    outfile.write("0\n")
        except (IOError, ValueError) as err:
            raise QBFDDError(err.strerror + ": " + filename)


    def _get_indices(self, subset, superset):
        """
        _get_indices(subset  : [...],
                     superset: [...])

        Return a list of superset-indices of all elements in subset.
        """
        index_list = []
        for item in subset:
            index_list.append(superset.index(item))
        assert(len(index_list) == len(subset))
        return index_list


    def _flatten_quants(self, quantsets):
        """
        _flatten_quants(quantsets: [[[], ...], ..., [ ..., []], ...]) 

        Return a 'flattened' list representing given quantset (does work for
        any other nested list as well), resulting list has one level only.
        """
        return list(self._flatten(copy.deepcopy(quantsets)))


    def _flatten(self, nested_list):
        """
        _flatten(nested_list: [[[], ...], ..., [ ..., []], ...])

        Generator for a flattened version of the given nested list.
        """
        for elem in nested_list:
            if type(elem) in (tuple,list):
                for e in self._flatten(elem):
                    yield e
            else:
                yield elem


    def _split(self, set, n):
        """
        _split(set : [...],
                n   : int)

        Split given set of clauses into n subsets;
        return a list of these n subsets.
        """
        assert(n > 0 and n <= len(set))
    
        subsets = []
        start = end = 0
        n_items = len(set)

        for i in range(0,n):
            start = end
            if i < n_items % n:
                end = start + n_items // n + 1
            else:
                end = start + n_items // n
            subsets.append(set[start:end])
    
        return subsets


    def _reduce(self, subsets, index, to_complement=True):
        """
        _reduce(subsets      : [[], ...],
                index        : int,
                to_complement: bool)

        Remove given subset from its superset (set of clauses);
        return a reduced set of clauses which is either equivalent to given
        subset or to its complement (to_complement=True) and the respectively 
        updated reference count array and set of quantsets.
        
        Note: returned values are not yet compatible with the QDIMACS standard -
              a call to _update() will solve this.
        """
        assert(len(self.clauses) >= 1)
        assert(len(subsets[index]) >= 1)
        # given subset must be an actual subset of given clauses list
        assert(False not in (subset_item in self.clauses for subset_item in 
               subsets[index]))

        subsets_list = subsets[:]
        clauses_red = []
        ref_count_red = self.ref_count[:]
        quantsets_red = []

        if not to_complement:
        # reduce to subset
            clauses_red = subsets_list.pop(index)
            for subset in subsets_list:
                for clause in subset:
                    for lit in clause:
                        ref_count_red[abs(lit)] -= 1
                        assert(ref_count_red[abs(lit)] >= 0)
        else:
        # reduce to complement
            subset = subsets_list.pop(index)
            for clause in subset:
                for lit in clause:
                    ref_count_red[abs(lit)] -= 1
                    assert(ref_count_red[abs(lit)] >= 0)
            for subset in subsets_list:
                clauses_red.extend(subset)

        if self.compliant:
            prev_quantifier = ''
            for quantset in self.quantsets:
                assert(len(quantset) == 2)
                quantset_red = [quantset[0], []]
                for lit in quantset[1]:
                    assert(lit > 0)
                    if ref_count_red[lit] != 0:
                       quantset_red[1].append(lit)

                if len(quantset_red[1]) > 0:
                    if prev_quantifier == quantset[0]:
                        assert(len(quantsets_red) >= 1)
                        quantsets_red[-1][1].extend(quantset_red[1])
                    else:
                        quantsets_red.append(quantset_red)
                        prev_quantifier = quantset[0]
        else:
            quantsets_red = copy.deepcopy(self.quantsets)

        return (ref_count_red, quantsets_red, clauses_red)


    def _minimize(self, clause, subsets, index, to_complement=True):
        """
        _minimize(clause       : [int, ...],
                  subset       : [int, ...]
                  to_complement: bool)

        Minimize given clause by removing given subset;
        return a minimized clause, which is either equivalent to given subset
        or its complement (to_complement=True) and the respectively updated 
        reference count array and set of quantsets.

        Note: returned values are not necessarily compatible with the QDIMACS
              standard - a call to _update() will solve this.
        """
        assert(len(clause) >= 1)
        assert(len(subsets[index]) >= 1)
        # given subset must be an actual subset of given clauses list
        assert(False not in (subset_item in clause for subset_item in 
               subsets[index]))
        
        subsets_list = subsets[:]
        clause_min = []
        ref_count_min = self.ref_count[:]
        quantsets_min = []

        if not to_complement:  
        # minimize to subset
            clause_min = subsets_list.pop(index)
            for subset in subsets_list:
                for lit in subset:
                    ref_count_min[abs(lit)] -= 1
                    assert(ref_count_min[abs(lit)] >= 0)
        else:                  
        # minimize to complement
            subset = subsets_list.pop(index)
            for lit in subset:
                ref_count_min[abs(lit)] -= 1
                assert(ref_count_min[abs(lit)] >= 0)
            for subset in subsets_list:
                clause_min.extend(subset)


        if self.compliant:
            prev_quantifier = ''
            for quantset in self.quantsets:
                assert(len(quantset) == 2)
                quantset_min = [quantset[0], []]
                for lit in quantset[1]:
                    assert(lit > 0)
                    if ref_count_min[lit] != 0:
                       quantset_min[1].append(lit)
                       
                if len(quantset_min[1]) > 0:
                    if prev_quantifier == quantset[0]:
                        assert(len(quantsets_min) >= 1)
                        quantsets_min[-1][1].extend(quantset_min[1])
                    else:
                        quantsets_min.append(quantset_min)
                        prev_quantifier = quantset[0]
        else:
            quantsets_min = copy.deepcopy(self.quantsets)

        return (ref_count_min, quantsets_min, clause_min)


    def _update(self, ref_count, quantsets, clauses):
        """
        _update(ref_count: [0, int, int, ...],
                quantsets: [[(e|a), [int, ...]], ...], 
                clauses  : [[int, ...], ...])

        Update given configuration to provide QDIMACS standard compliance;
        return ref count, quantsets and clauses made standard compliant 
        accordingly:
            - variables are named consecutively (from 1 to n, where n is the 
              total number of variables)
            - contiguous quantified sets are not bound by the same quantifier
            - each atom appearing in the prefix, also appears in the matrix
            - the innermost quantified set is always of type 'e'
        """
        assert(len(clauses) >= 1)
        ref_count_upd = [0]           # ref_count[0] = 0: dummy element
        clauses_upd = []
        quantsets_upd = []
        mapping = [0]                 # mapping[0] = 0: dummy element
        
        assert(not (len(quantsets) == 1 and quantsets[-1][0] == 'a'))

        # eliminate variables bound by innermost scope if universal
        if len(quantsets) != 0 and quantsets[-1][0] == 'a':
            (ref_count, quantsets, clauses) = \
                self._forall(ref_count, quantsets, clauses)

        if ref_count.count(0) > 1:
            # update ref count and create mapping table:
            # mapping[i]: lit (old value) at index i (updated value)
            for i in range(0, len(ref_count)):
                if ref_count[i] != 0:
                    ref_count_upd.append(ref_count[i])
                    mapping.append(i)

            # update quantsets
            for quantset in quantsets:
                updated_quantset = [quantset[0], []]
                for lit in quantset[1]:
                    assert(lit > 0)
                    if (ref_count[lit] != 0):
                        updated_quantset[1].append(mapping.index(lit))
                if (len (updated_quantset[1]) > 0):
                    quantsets_upd.append(updated_quantset)

            # update clauses
            for clause in clauses:
                assert(len(clause) >= 1)
                updated_clause = []
                for lit in clause:
                    assert(ref_count[abs(lit)] != 0)
                    updated_clause.append(
                            int(math.copysign(mapping.index(abs(lit)), lit)))
                assert(len(updated_clause) >= 1)
                clauses_upd.append(updated_clause)
        else:
            ref_count_upd = ref_count[:]
            quantsets_upd = copy.deepcopy(quantsets)
            clauses_upd = clauses[:]

        for quantset in quantsets_upd:
            quantset[1].sort()

        return (ref_count_upd, quantsets_upd, clauses_upd)



    def _swap(self, index):
        """
        _swap(index: int)

        Swap quantifier of given quantset with its counterpart - a universal
        quantifier is replaced by an existential and vice versa, contiguous
        quantifier sets bound by the same quantifier are merged;
        return the accordingly modified set of quantifier sets.
        """
        assert(len(self.quantsets) > index)
        quantsets_swap = copy.deepcopy(self.quantsets)
        quantifier = self.quantsets[index][0]
        assert(quantifier == 'a' or quantifier == 'e')

        if quantifier == 'a':
            quantifier = 'e'
        else:
            quantifier = 'a'

        if index > 0 and index < len(self.quantsets) - 1:
            assert(self.quantsets[index][0] != self.quantsets[index+1][0])
            assert(self.quantsets[index][0] != self.quantsets[index-1][0])
            quantsets_swap[index-1][1].extend(self.quantsets[index][1])
            quantsets_swap[index-1][1].extend(self.quantsets[index+1][1])
            quantsets_swap[index-1][1].sort()
            quantsets_swap[index-1][0] = quantifier
            quantsets_swap.pop(index+1)
            quantsets_swap.pop(index)
        elif index > 0:  # last element
            assert(self.quantsets[index][0] != self.quantsets[index-1][0])
            quantsets_swap[index-1][1].extend(self.quantsets[index][1])
            quantsets_swap[index-1][1].sort()
            quantsets_swap[index-1][0] = quantifier
            quantsets_swap.pop(index)
        else:            # first element
            if index < len(self.quantsets) - 1:
                assert(self.quantsets[index][0] != self.quantsets[index+1][0])
                quantsets_swap[index][1].extend(self.quantsets[index+1][1])
                quantsets_swap[index][1].sort()
                quantsets_swap.pop(index+1)
            quantsets_swap[index][0] = quantifier
        return quantsets_swap


    def _forall(self, ref_count, quantsets, clauses):
        """
        _forall(ref_count: [0, int, int, ...],
                quantsets: [[(e|a), [int, ...]], ...], 
                clauses  : [[int, ...], ...])

        Eliminate variables bound by innermost scope if it is universal;
        return a respectively updated configuration (ref count, quantsets
        and clauses).
        
        Note, that this is not a forall reduction by the textbook but a 
        simplified variant: All universal literals bound by the innermost 
        scope are discarded, tautologies and conflicting clauses are basically 
        treated the same - therefore both may result in empty clauses, which 
        are eliminated without further consequencs.
        
        This simplification is legal due to the following:
            - this procedure is mainly to be applied to configurations,
              that break QDIMACS standard compliance by a universal innermost
              scope (that is, to make the configuration standard compliant)
            - in terms of delta debugging, it is not important whether the
              resulting formula is semantically the same as the original one -
              as long as it's simpler/smaller and triggers the same faulty
              behaviour.
            - it's legitimate to assume, that empty clauses are very likely
              to not trigger the same faulty behaviour as the original input
        """
        assert(quantsets[-1][0] == 'a')
        quantsets_fa = copy.deepcopy(quantsets)
        clauses_fa = copy.deepcopy(clauses)
        ref_count_fa = ref_count[:]

        for var in quantsets[-1][1]:
            assert(var >= 0)
            assert(ref_count_fa[var] > 0)
            i = 0
            while i < len(clauses_fa):
                while clauses_fa[i].count(var):
                    clauses_fa[i].remove(var)
                    ref_count_fa[var] -= 1
                while clauses_fa[i].count(-var):
                    clauses_fa[i].remove(-var)
                    ref_count_fa[var] -= 1
                if not clauses_fa[i]:  # empty
                    clauses_fa.pop(i)
                else:
                    i += 1

        assert(ref_count_fa[var] == 0)
        quantsets_fa.pop()  # remove last quantset
        return(ref_count_fa, quantsets_fa, clauses_fa)


    def _shift(self):
        """
        Manipulate quantifier sets;
        first try if any swap is successful - if not, proceed with shifting
        variables from one quantifier set to another;
        return True if successful, False otherwise.
        """
        successful = False
        # quantifier swaps
        for i in range(len(self.quantsets)):
            quants = self._swap(i)
            
            quants_list = self._flatten_quants(quants)
            if self.quants_cache.look_up(quants_list):
                continue

            ref_count_upd = self.ref_count
            quantsets_upd = quants
            clauses_upd = self.clauses

            if self.compliant:
                # check if innermost quantifier is universal  
                # note: this may also occur in original innermost quantset
                # as QBFParser is NOT strictly QDIMACS standard compliant!
                if quants[-1][0] == 'a':
                    if len(quants) == 1:
                        if self.verbose > 1:
                            print("only one universal quantset left, skipping" \
                                  "test run")
                        continue
                    if self.verbose > 1:
                        start_upd = time.time()
                        print("updating in order to be QDIMACS compliant "\
                              "(for-all)...", end='')
                        sys.stdout.flush()

                    (ref_count_upd, quantsets_upd, clauses_upd) = \
                        self._update(self.ref_count, quants, self.clauses)
                    
                    if self.verbose > 1:
                        print("\t\t{0}{1:7.2f}ms{2}".format(
                                  self.gray, (time.time() - start_upd) * 1000, 
                                  self.std))
            
            # write file for test run
            if self.verbose > 1:
                start_write = time.time()
                print("writing new configuration to output file...", end='')
                sys.stdout.flush()
           
            self._write_file(self.tmpfile, 
                             len(ref_count_upd) - 1, quantsets_upd, clauses_upd)
            
            if self.verbose > 1:
                print("\t\t\t{0}{1:7.2f}ms{2}".format(
                      self.gray, (time.time() - start_write) * 1000, self.std))
                start_test = time.time()

            # test run
            test_result = self._test()

            if self.verbose > 1:
                print("test run: {0:4d}\t".format(self.test_runs), end='')
                sys.stdout.flush()
            
            self.quants_cache.add(quants_list, test_result)

            if test_result == self.FAILED:
                if self.compliant:
                    self.num_vars = len(self.ref_count) - \
                                    self.ref_count.count(0)
                self.quantsets = quants[:]
                successful = True
                
                # save successful config
                self._write_file(self.outfile, len(ref_count_upd) - 1, 
                                 quantsets_upd, clauses_upd)

                if self.verbose > 1:
                    print("\t{0}successful{1}\t\t\t\t{2}{3:7.2f}ms" \
                          "{4}".format(self.green, self.std, self.gray, 
                                       (time.time() - start_test) * 1000, 
                                       self.std))
                break
            elif self.verbose > 1:
                print("\t{0}not successful{1}\t\t\t\t{2}{3:7.2f}ms" \
                      "{4}".format(self.red, self.std, self.gray, 
                                   (time.time() - start_test) * 1000, 
                                   self.std))
        # end for

        if not successful:
            # quantifier shifts
            for i in range(len(self.quantsets)):
                if len(self.quantsets[i][1]) <= 1:  # already tested (swaps)
                    continue

                vars = self.quantsets[i][1][:]
                for j in range(len(vars)):
                    to_prev = False
                    to_next = False
                    if i > 0:
                        to_prev = True
                    if i < len(self.quantsets) - 1:
                        to_next = True
                    while 1:
                        if to_prev:
                            # move quantsets[i][1][j] == vars[j] to previous
                            quants = copy.deepcopy(self.quantsets)
                            quants[i-1][1].append(vars[j])
                            quants[i][1].pop(j)
                            to_prev = False
                        elif to_next:  # and not to_prev!
                            # move quantsets[i][1][j] == vars[j] to next
                            quants = copy.deepcopy(self.quantsets)
                            quants[i+1][1].append(vars[j])
                            quants[i][1].pop(j)
                            to_next = False
                        else:
                            break
                        
                        quants_list = self._flatten_quants(quants)
                        if self.quants_cache.look_up(quants_list):
                            continue

                        # write file for test run
                        # note: no need to update (it's just vars being shifted)
                        if self.verbose > 1:
                            start_write = time.time()
                            print("writing new configuration to output file...",
                                  end='')
                            sys.stdout.flush()
                       
                        self._write_file(self.tmpfile, 
                                         len(self.ref_count) - 1,
                                         quants, 
                                         self.clauses)
                        
                        if self.verbose > 1:
                            print("\t\t\t{0}{1:7.2f}ms{2}".format(
                                      self.gray, 
                                      (time.time() - start_write) * 1000,
                                      self.std))
                            start_test = time.time()

                        # test run
                        test_result = self._test()

                        if self.verbose > 1:
                            print("test run: {0:4d}\t".format(self.test_runs), 
                                  end='')
                            sys.stdout.flush()
                        
                        self.quants_cache.add(quants_list, test_result)

                        if test_result == self.FAILED:
                            self.quantsets = quants[:]
                            successful = True
                            # save successful config 
                            self._write_file(self.outfile, 
                                             len (self.ref_count) - 1,
                                             quants, 
                                             self.clauses)

                            if self.verbose > 1:
                                print("\t{0}successful{1}\t\t\t\t{2}" \
                                      "{3:7.2f}ms{4}".format(
                                          self.green, self.std, self.gray, 
                                          (time.time() - start_test) * 1000, 
                                          self.std))
                            break
                        elif self.verbose > 1:
                            print("\t{0}not successful{1}\t\t\t\t{2}" \
                                  "{3:7.2f}ms{4}".format(
                                      self.red, self.std, self.gray, 
                                      (time.time() - start_test) * 1000, 
                                      self.std))
                    # end while    
                    if successful:  # done
                        break
                # end for
                if successful:
                    break  # done
            # end for
        return successful


class Cache:
    """Simple cache implementation for test results of previous test runs."""
    def __init__(self):
        self.cache = {}

    def hash(self, list):
        # treat each configuration unique with respect to the order of list 
        # items -> list remains unsorted
        s = ''
        for item in list:
            s += str(item) + '#'
        return s

    def add(self, list, test_result):
        key = self.hash(list)
        self.cache[key] = test_result

    def look_up(self, list):
        key = self.hash(list)
        try:
            result = self.cache[key]
        except KeyError:
            result = None
        return result


class QBFParseError(Exception):
    """Raised when any error while parsing the input file occurs."""
    
    def __init__(self, msg, filename, num_lines):
        if num_lines:
            self.msg = filename + ":" + str(num_lines) + ": " + msg
        else:
            self.msg = filename + ": " + msg

    def __str__(self):
        return("[ERROR] " + self.msg)


class QBFParser:
    """
    QBFParser is a parser for QBF in QDIMACS format.
    
    Input files to be parsed by QBFParser don't have to be strictly QDIMACS 
    standard compliant, but the following basic rules have to be obeyed:
        - basic structure:
            + unspecified numer of comments of the form: c <string>
            + valid header: p cnf <pnum> <pnum> EOL
                            where pnum > 0 and EOL = '0'
            + quantifier sets, quantifiers must be either 'e' or 'a' 
            + clauses
        - all input (comments, header, quantifier sets and clauses) must follow
          the grammatical structure defined in QDIMACS standard version 1.1
          (see http://www.qbflib.org/qdimacs.html#input)
        - given quantifier sets must be alternating
        - empty quantsets are not allowed
        - given number of clauses and number of clauses given must match

    Anything else not specified above may be considered as allowed and valid.
    """ 

    BLANK_LINE = [""]
    
    def parse_file(self, filename):
        """
        parse_file(filename: string)

        Parse given input file;
        return the number of variables, a list with the number of their resp.
        appearance (the so called reference count), the set of quantifier sets
        and the set of clauses if given input is valid;
        raise QBFParseError otherwise.
        """ 
        quantsets = []
        clauses = []
        ref_count = []

        num_quantsets = num_clauses = num_lines = 0
        pattern = re.compile("\s+")
        
        try:
            with open(filename, 'r') as infile:
                # comments
                for line in infile:
                    num_lines += 1
                    l = pattern.split(line.strip())
                    if l[0] != 'c' and l != self.BLANK_LINE:
                        break

                # header
                if l[0] != 'p' or l[1] != "cnf" or len(l) != 4:
                    if l[0] == 'a' or l[0] == 'e':
                        raise QBFParseError("missing header", filename, 
                                            num_lines)
                    raise QBFParseError("invalid header", filename, num_lines)

                try:
                    num_vars = int(l[2])
                    if num_vars <= 0:
                        raise QBFParseError("invalid number of variables", 
                                             filename, num_lines);
                    # initialise var count, ref_count[0] will never be used
                    # (all counts are directly referenced)
                    ref_count = [0 for i in range(0, num_vars+1)]
                    
                    num_clauses = int(l[3])
                    if num_clauses <= 0:
                        raise QBFParseError("invalid number of clauses", 
                                            filename, num_lines);
                except ValueError as err:
                    raise QBFParseError(str(err), num_lines)
                
                # quantifier sets
                prev_quantifier = ''

                for line in infile:
                    num_lines += 1
                    l = pattern.split(line.strip())
                    
                    if l == self.BLANK_LINE:
                        continue

                    if l[0] != 'e' and l[0] != 'a':
                        break
                    
                    if l[-1] != '0':
                        raise QBFParseError("missing '0' after quantset", 
                                             filename, num_lines)
                    elif len(l) == 2:
                        raise QBFParseError("empty quantset", filename, 
                                            num_lines)
                        
                    quantset = [l[0]]
                    if quantset[0] == prev_quantifier:
                        raise QBFParseError("quantifiers given must be " \
                                            "alternating", filename, num_lines)
                    prev_quantifier = quantset[0]

                    try:
                        quantset.append(
                                [self._parse_literal(l_item, 1, num_vars) 
                                for l_item in l[1:-1]])
                        quantsets.append(quantset)
                        num_quantsets += 1
                    except ValueError as err:
                        raise QBFParseError(str(err), filename, num_lines)
                else:
                     raise QBFParseError("missing clause definitions", 
                                          filename, num_lines)
                # clauses
                if l != self.BLANK_LINE:  # first clause (already been read)
                    if l[-1] != '0':
                        raise QBFParseError("missing '0' after clause", 
                                             filename, num_lines)
                    try:
                        clause = []
                        for l_item in l[:-1]:
                            lit = self._parse_literal(l_item, -num_vars, 
                                                      num_vars)
                            clause.append(lit)
                            ref_count[abs(lit)] += 1
                        clauses.append(clause)
                        
                    except ValueError as err:
                        raise QBFParseError(str(err), filename, num_lines)

                for line in infile:  # remaining clauses
                    num_lines += 1
                    l = pattern.split(line.strip())
                    
                    if l == self.BLANK_LINE: 
                        continue
                    if l[-1] != '0':
                        raise QBFParseError("missing '0' after clause", 
                                             filename, num_lines)
                    try:
                        clause = []
                        for l_item in l[:-1]:
                            lit = self._parse_literal(l_item, -num_vars, 
                                                      num_vars)
                            clause.append(lit)
                            ref_count[abs(lit)] += 1
                        clauses.append(clause)
                    except ValueError as err:
                        raise QBFParseError(str(err), num_lines)
                    # optimization: skip last quantset if universal

                if len(clauses) > num_clauses:
                    raise QBFParseError("too many clauses given", 
                                        filename, num_lines)
                elif len(clauses) < num_clauses:
                    raise QBFParseError("not enough clauses given", 
                                        filename, num_lines)
                return (num_vars, ref_count, quantsets, clauses)
            # end with
        except IOError as err:
            raise QBFParseError("could not open file", filename, 0)


    def _parse_literal(self, lit, range_from, range_to):
        """
        _parse_literal(lit        : string, 
                       range_from : int, 
                       range_to   : int)

        Convert given literal to integer and check if it is valid (within
        given range);
        return resp. integer if it is; 
        raise ValueError otherwise.
        """
        try:
            value = int(lit)
        except ValueError as err:
           raise ValueError("invalid literal: '" + lit + "'")
        
        if value == 0:
            raise ValueError("invalid literal: '0'")
        
        if value < range_from or value > range_to:
            raise ValueError("invalid literal, not within range [{},{}]: " \
                             "{}".format(range_from, range_to, lit))
        return value


class QBFOptionParserFormatter(IndentedHelpFormatter):
    """Format help text with new-lines preserved."""

    def format_description(self, description):
        if description:
            desc = description.splitlines()
            res = [textwrap.wrap(desc_item, self.width - self.current_indent)
                   for desc_item in desc]
            res = ["\n".join(res_item) for res_item in res]
            return "\n".join(res) + "\n"
        else:
            return ""


class QBFOptionParser(OptionParser):
    """
    QBFOptionParser is the option parser for QBFDD.
    
    This is an extended version of the original (with respect to help text 
    display for command line arguments) and provides configuration details for 
    all command line options and arguments taken as valid by QBFDD.
    """
    
    def __init__(self, version):
        usg = "%prog [options] INFILE \"CMD [options]\""
        desc = ("QBFDD serves as an input minimizer for failing QBF solvers " \
                "by removing as many clauses and literals from given input " \
                "file as possible without making the given solver pass on " \
                "the minimized input.\n\n" \
                "QBFDD provides several different minimization modes, " \
                "depending on the minimization strategies used.\n" \
                "Currently available: \tddmin [1], sddmin [2], " \
                "iddmin [3], isddmin [4],\n\t\t\tobo [5], qobo [6]\n\n" \
                "Note, that it is possible to define three levels of " \
                "granularity for each minimization strategy: c (clauses " \
                "only), l (literals only), b (both)\n\n"
                "[1] A. Zeller, R. Hildebrandt: Simplifying " \
                "failure-inducing input, ISSTA 2000\n" \
                "[2] A. Zeller: Why programs fail, ISBN 3-89864-279-8, dpunkt" \
                " Verlag, 2006\n" \
                "[3] inverse version of [1]\n[4] inverse version of [2]\n" \
                "[5] one by one\n[6] quick obo")

        formatter = QBFOptionParserFormatter()
        OptionParser.__init__(self, usage=usg, description=desc, 
                                    formatter=formatter, version=version)
        self.add_option("-f", "--failed", dest="failed", metavar="val",
                        type="int",
                        help="solver's return value, failing on given input")
        self.add_option("-p", "--passed", dest="passed", metavar="val",
                        type="int",
                        help="solver's return value, passing given input")
        self.add_option("-o", "--out", 
                        dest="outfile", metavar="file",
                        help="individual file name for minimized QBF")
        self.set_defaults(outfile=None)
        self.add_option("-O", "--tmp",
                        dest="tmpfile", metavar="file",
                        help="individual file name for temp work file")
        self.set_defaults(tmpfile=None)
        self.add_option("-m", "--mode", dest="mode", metavar="str", 
                        default="ddmin",
                        help="minimization strategy used (default: %default)")
        self.add_option("-g", "--gran", dest="gran", metavar="char", 
                        default='b', 
                        help="minimization granularity used "\
                             "(default: %default)")
        self.add_option("-s", "--shift", action="store_true", 
                        dest="shift", default=False,
                        help="enable quantifier manipulations (shifts from " \
                             "one quantset to another)")
        self.add_option("-S", "--skip-output", action=("store_true"),
                         dest="skip", default=False,
                         help="don't care about stdout and stderr when "\
                              "determining test run results")
        self.add_option("-t", "--timeout", dest="timeout", metavar="val",
                        default=0, type="int",
                        help="timeout for test runs in seconds (default: none)")
        self.add_option("-q", "--no-qdimacs", action="store_false", 
                        dest="compliant", default=True,
                        help="don't try to be QDIMACS standard compliant")
        self.add_option("-c", "--no-color", action="store_false",
                        dest="use_bash_colors", default=True,
                        help="disable color output")
        self.add_option("-v", "--verbose", action="count", 
                        dest="verbose", default=False,
                        help="don't be quiet and print status to stdout, " \
                             "multiple occurences of this option increase " \
                             "level of verbosity")

    def error(self, msg):
        """
        error(msg : string)

        Print a usage message incorporating 'msg' to stderr and exit.
        This is an override of the OptionParser's error() in order to make
        error messages used in QBFDD look homogenous.
        """
        self.print_usage(sys.stderr)
        self.exit(2, "[ERROR] {0}\n".format(msg))


    def format_help(self, formatter=None):
        """
        format_help(formatter : HelpFormatter)

        Override and extend the OptionParser's format_help() in order to be 
        able to print formatted help for positional arguments.
        """
        return OptionParser.format_help(self) + self.get_args_help() + "\n"


    def get_args_help(self):
        """Help string for arguments to be passed to QBFDD."""
        gap = "               "
        return ("\nArguments:\n" +
               "  INFILE" + gap + "input file in QDIMACS format\n" +
               "  CMD   " + gap + "call to QBF solver, options included\n")





if __name__ == "__main__":
    opt_parser = QBFOptionParser(__version__)
    (options, args) = opt_parser.parse_args()
    
    if len(args) != 2:
        opt_parser.error("invalid number of arguments")

    try:
        qbf_dd = QBFDD(args[0], args[1], options.outfile, options.tmpfile,
                       options.failed, options.passed, options.mode, 
                       options.gran, options.verbose, options.compliant, 
                       options.shift, options.skip, options.timeout, 
                       options.use_bash_colors)
        qbf_dd.dd()
        sys.exit()
    except (KeyboardInterrupt) as err:
        if os.path.exists(qbf_dd.outfile):
            os.remove(qbf_dd.tmpfile)
        sys.exit(err)
