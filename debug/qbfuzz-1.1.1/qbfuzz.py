#! /usr/bin/env python3
#
# QBFuzz is a grammar based black box fuzzer for generating random QBF formulas.
#
# Copyright (c) 2009, 2010, 2011 Mathias Preiner
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
#
import gzip
import os
import math
import random
import sys
import time
from optparse import OptionParser

__author__ = "Mathias Preiner <mathias.preiner@gmail.com>"
__version__ = "1.1.1"

# constants
UNIVERSAL = 'a'
EXISTENTIAL = 'e'
USED = 0
UNUSED = 1

# global program parameters
_options = object

# variables used for statistics only (verbose output)
_stat_removed_lits = 0
_stat_total_lits = 0

# quantifier cache: stores information about all existential and universal 
#                   variables if they have already been used or not in clause
#                   generation. variable cache is not used for this because 
#                   the lookup in the variable cache would take much more time.
_qcache = {EXISTENTIAL : {}, UNIVERSAL : {}}
_qcache[EXISTENTIAL][UNUSED] = []
_qcache[EXISTENTIAL][USED] = []
_qcache[UNIVERSAL][UNUSED] = []
_qcache[UNIVERSAL][USED] = []

# variable cache: stores a list containing quantifier, scope level and number
#                 of occurrences for each variable.
# list indices:
# _vcache[var][0] : quantifier
# _vcache[var][1] : scope level
# _vcache[var][2] : number of occurrences in all clauses
_vcache = {}

def _parse_arguments():
    """
    _parse_arguments()

    returns (p   : OptionParser object,
             opt : OptionParser options)

    Initialize OptionParser object with all available QBFuzz options.

    Returns parser object and parsed options.
    """
    global __version__

    description = "QBFuzz is a grammar based black box fuzzer for generating "\
                  "random QBF formulas compliant to the QDIMACS standard. The "\
                  "program uses random parameter values if none are specified."

    p = OptionParser(description=description, version=__version__)

    # number of variables
    p.add_option("-v", type="int", dest="num_vars", metavar="NUM",\
                 help="maximum number of variables")
    # number of clauses
    p.add_option("-c", type="int", dest="num_clauses", metavar="NUM",\
                 help="maximum number of clauses")
    # number of quantifier sets
    p.add_option("-s", type="int", dest="num_qsets", metavar="NUM",\
                 help="maximum number of quantifier sets")
    # name of the output file
    p.add_option("-o", type="string", dest="filename", metavar="FILE",\
                 help="name of the output file [default: stdout]. if "\
                      "compression is enabled, file extension will be "\
                      "automatically appended.")
    # existential variable ratio (existential variables/total variables)
    p.add_option("-r", type="float", dest="ratio", metavar="FLOAT",\
                 help="ratio of the overall number of existential variables. "\
                      "it is also used for clause generation.")
    # ratio of free variables
    p.add_option("-f", type="float", dest="free_ratio", metavar="FLOAT",\
                 help="ratio of free variables")
    # minimum number of literals per clause
    p.add_option("--min", type="int", dest="min_lits", metavar="NUM",\
                 help="minimum number of literals per clause")
    # maximum number of literals per clause
    p.add_option("--max", type="int", dest="max_lits", metavar="NUM",\
                 help="maximum number of literals per clause")
    # seed for random number generator
    p.add_option("--seed", type="int", dest="seed", metavar="NUM",\
                 help="use this seed for random generator")
    # disable forall reduction
    p.add_option("--no-reduce", action="store_false", default=True,\
                 dest="reduce", help="disable forall reduction")
    # allow unit clauses
    p.add_option("--unit-clauses", action="store_true", default=False,\
                 dest="allow_unit", help="allow unit clauses")
    # enable verbose output
    p.add_option("--verbose", action="store_true", default=False,\
                 dest="verbose", help="print verbose status messages")
    # sort literals according to scope levels
    p.add_option("--sort", action="store_true", default=False, dest="sort",\
                 help="sort literals in clause according to scope levels")
    # compress output file using gzip
    p.add_option("--gzip", action="store_true", default=False, dest="gzip",\
                 help="enable gzip compression for output file "\
                      "(only with -o)")

    (opt, args) = p.parse_args()

    return (p, opt)

def _init(comments):
    """
    _init(comments : list)

    returns (opt     : OptionParser options,
             outfile : file)
           
    Checks given parameters and generates random values for mandatory
    parameters if they have not been specified. Further, generation time,
    version of QBFuzz and parameter values used for generation are appended to 
    the comments.

    Returns the parameters and the output file.
    """
    global _options

    (parser, _options) = _parse_arguments()
    
    # maximum ranges of random values
    MAX_VARS = 200
    MAX_CLAUSES = 1000
    MAX_QSETS = 5
    MAX_LITS = 15

    # initialize random seed generator
    if _options.seed == None:
        # multiply current process id with current unix timestamp and convert
        # number to a 32 bit integer
        _options.seed = int(time.time() * os.getpid() % (2**32))
    # set seed of random generator
    random.seed(_options.seed)
    
    # save parameters for reproducing generated formula
    gen_params = "qbfuzz.py --seed={0:d}".format(_options.seed)

    # allow unit clauses if minimum/maximum number of literals per clause is 
    # excplicitely set to one
    if _options.min_lits == 1 or _options.max_lits == 1:
        _options.allow_unit = True

    # number of variables
    if _options.num_vars == None:
        # if unit clauses are allowed, number of variables can be >= 1
        if _options.allow_unit:
            lo_bound = 1
        else:
            lo_bound = 2
        _options.num_vars = random.randint(lo_bound, MAX_VARS)
    else:
        if _options.allow_unit:  
            if _options.num_vars <= 0:
                parser.error("number of variables has to be greater 0")
        else:
            if _options.num_vars <= 1:
                parser.error("number of variables has to be greater 1")

        gen_params += " -v {0:d}".format(_options.num_vars)
    
    if _options.ratio != None:
        # check if given ratio is valid
        if _options.ratio < 0.0 or _options.ratio > 1.0:
            parser.error("ratio has to be between 0.0 and 1.0")
        elif _options.ratio == 0.0 and _options.reduce:
            parser.error("ratio will produce empty formula. retry with "\
                         "--no-reduce")

        # calculate number of existential and universal variables if ratio is 
        # given
        ex_vars = max(1, math.floor(_options.num_vars * _options.ratio))
        un_vars = _options.num_vars - ex_vars

    # generate random number of clauses
    if _options.num_clauses == None:
        if _options.ratio != None:
            lo_bound = max(ex_vars, un_vars)
        else:
            lo_bound = 1
            
        _options.num_clauses = random.randint(lo_bound, \
                                              max(lo_bound, MAX_CLAUSES))
    else:
        if _options.num_clauses <= 0:
            parser.error("number of clauses has to be greater 0")

        gen_params += " -c {0:d}".format(_options.num_clauses)

    # generate random number of quantifier sets
    if _options.num_qsets == None:
        lo_bound = 1
        # if ratio is enabled there have to be at least two quantifier sets 
        # except with ratio = 1.0 and ratio = 0.0
        if _options.ratio != None:
            if _options.ratio > 0.0 and _options.ratio < 1.0:
                lo_bound = 2

        if _options.num_vars == 1:
            _options.num_qsets = 1
        else:
            _options.num_qsets = random.randint(lo_bound, \
                                    min(_options.num_vars, MAX_QSETS))
        
        assert(_options.num_qsets <= _options.num_vars)
    else:
        if _options.num_qsets <= 0:
            parser.error("number of quantifier sets has to be greater 0")
        elif _options.num_qsets > _options.num_vars:
            parser.error("number of quantifier sets cannot be greater than "\
                         "the number of variables")
        gen_params += " -s {0:d}".format(_options.num_qsets) 
    
    # existential variable ratio
    if _options.ratio != None:
        # calculate number of maximal existential and universal quantifier sets
        num_ex_sets = num_un_sets = math.ceil(_options.num_qsets / 2)

        # invalid ratio if produced existential variables are not 0 or num_vars
        # for one possible quantifier set
        if _options.num_qsets == 1 and ex_vars != _options.num_vars and \
           ex_vars != 0:
            parser.error("invalid ratio for only one quantifier set")
        # not enough variables for given number of quantifier sets
        elif _options.ratio > 0.0 and _options.ratio < 1.0 and \
             (ex_vars < num_ex_sets or un_vars < num_un_sets):

            parser.error("it is not possible to produce enough variables for "\
                         "all existential and universal quantifier sets using"\
                         " given ratio. retry with another combination of "\
                         "ratio and sets.")

        gen_params += " -r {0:.2f}".format(_options.ratio)

    # free variable ratio
    if _options.free_ratio != None:
        if _options.free_ratio < 0.0 or _options.free_ratio > 1.0:
            parser.error("free variable ratio has to be between 0.0 and 1.0")

        gen_params += " -f {0:.2f}".format(_options.free_ratio)

    # minimum number of literals per clause
    if _options.min_lits == None:
        # only allow --min=1 if no ratio is specified or if all variables are
        # existential or universal. otherwise there is no guarantee to use all
        # variables for generating clauses
        if _options.allow_unit and \
           (_options.ratio == None or _options.ratio == 1.0 or \
            _options.ratio == 0.0):
            lo_bound = 1
        else:
            lo_bound = 2
        _options.min_lits = max(lo_bound, math.ceil(_options.num_vars / 
                                                    _options.num_clauses))

        assert(_options.min_lits <= _options.num_vars)
    else:
        if _options.min_lits <= 0:
            parser.error("minimum number of literals per clause has to be "\
                         "greater 0")
        elif _options.min_lits > _options.num_vars:
            parser.error("minimum number of literals per clause cannot be "\
                         "greater than the number of variables")
        elif _options.min_lits < math.ceil(_options.num_vars / 
                                           _options.num_clauses):
            parser.error("it is not possible to generate a valid formula "\
                         "using this sequence of parameters. try --min={0:d} "\
                         "or higher"\
                         .format(math.ceil(_options.num_vars / 
                                           _options.num_clauses)))
        elif _options.min_lits == 1 and _options.ratio != None:
            # --min=1 only allowed if all variables are exitential or universal
            if _options.ratio > 0.0 and _options.ratio < 1.0:
                parser.error("it is not possible to generate clauses with a "\
                             "minimum of one literal and a ratio of {0:.2f}"\
                             .format(_options.ratio))

        gen_params += " --min={0:d}".format(_options.min_lits)

    # maximum number of literals per clause
    if _options.max_lits == None:
        _options.max_lits = random.randint(_options.min_lits,
                                max(_options.min_lits,
                                    min(_options.num_vars, MAX_LITS)))
        assert(_options.max_lits <= _options.num_vars)
        assert(_options.max_lits >= _options.min_lits)
    else:
        if _options.max_lits <= 0:
            parser.error("maximum number of literals per clause has to be "\
                         "greater 0")
        elif _options.max_lits > _options.num_vars:
            parser.error("maximum number of literals per clause cannot be "\
                         "greater than the number of variables")
        elif _options.max_lits < _options.min_lits:
            parser.error("maximum number of literals per clause has to be "\
                         "greater than the minumum number of literals")
        elif _options.max_lits == 1 and _options.ratio != None:
            # --max=1 only allowed if all variables are exitential or universal
            if _options.ratio > 0.0 and _options.ratio < 1.0:
                parser.error("it is not possible to generate clauses with a "\
                             "maximum of one literal and a ratio of {0:.2f}"\
                             .format(_options.ratio))

        gen_params += " --max={0:d}".format(_options.max_lits)

    if _options.ratio != None:
        if _options.ratio > 0.0 and _options.ratio < 1.0:
            # minimum number of variables used in all clauses (worst case)
            ex_lits = max(1, math.floor(_options.min_lits * _options.ratio)) \
                      * _options.num_clauses
            un_lits = (_options.min_lits * _options.num_clauses) - ex_lits

            if ex_lits < ex_vars or un_lits < un_vars:
                parser.error("it is not possible to use all existential and "\
                             "universal variables in the given number of "\
                             "clauses. try -c {0:d} or more"\
                             .format(max(ex_vars, un_vars)))
       
    # output file
    if _options.filename == None:
        if _options.gzip:
            parser.error("compression only available with -o parameter")
 
        outfile = sys.stdout
    else:
        gen_params += " -o {0:s}".format(_options.filename)
        try:
            # no gzip compression
            if not _options.gzip: 
                outfile = open(_options.filename, "w")
            # gzip compression
            else:
                gen_params += " --gzip"
                try:
                    outfile = gzip.open("{0:s}.gz".format(_options.filename), \
                                        "wb")
                except gzip.CompressionError:
                    parser.error("compression method 'gzip' is not supported "\
                                 "on this system")
        except IOError:
            parser.error("could not open file")

    # do not apply forall reduction
    if not _options.reduce:
        gen_params += " --no-reduce"

    # allow unit clauses
    if _options.allow_unit:
        gen_params += " --unit-clauses"

    # verbose messages
    if _options.verbose:
        gen_params += " --verbose"

    # sort literals
    if _options.sort:
        gen_params += " --sort"
   
    # save generation time and parameters as comments
    comments.append("generated {0:s} with QBFuzz version {1:s}"\
                    .format(time.strftime("%m-%d-%Y %H:%M:%S"), __version__))
    comments.append(gen_params)

    return outfile


def _write_file(outfile, comments, num_vars, quantsets, clauses):
    """
    _write_file(outfile   : file,
                  comments  : list,
                  num_vars  : int,
                  quantsets : list,
                  clauses   : list)

    Writes given comments and formula to the output file.
    """
    # write comments
    comments.append("")
    for comment in comments:
        outfile.write("c {0:s}\n".format(comment))

    # write problem line
    outfile.write("p cnf {0:d} {1:d}\n".format(num_vars, len(clauses)))

    # write quantifier sets
    for qset in quantsets:
        for literal in qset:
            outfile.write("{0:s} ".format(str(literal)))
        outfile.write("0\n")

    # write clauses
    for clause in clauses:
        for literal in clause:
            outfile.write("{0:d} ".format(literal))
        outfile.write("0\n")

    # close file
    if outfile != sys.stdout:
        outfile.close()

def _get_quantifier(literal):
    """
    _get_quantifier(literal : int)

    return (UNIVERSAL or EXISTENTIAL)

    Returns quantifier of given literal.
    """
    global _vcache

    assert(literal > 0 or literal < 0)
    return _vcache[abs(literal)][0]

def _get_scope_level(literal):
    """
    _get_scope_level(literal : int)

    return (scope level of literal : int)

    Returns scope level of given literal.
    """
    global _vcache

    assert(literal > 0 or literal < 0)
    return _vcache[abs(literal)][1]

def _get_occs_cnt(literal):
    """
    _get_occs_cnt(literal : int)

    return (occurence count of literal : int)
    
    Returns the occurence count of given literal (positive + negative 
    occurences).
    """
    global _vcache
    
    assert(literal > 0 or literal < 0)
    return _vcache[abs(literal)][2]


def _sort_by_scope(clause):
    """
    _sort_by_scope(clause : list)

    return (sorted_clause : list)

    Sorts the given clause by quantifier scope levels and returns the 
    sorted clause.

    Returns the sorted clause.
    """
    assert(len(clause) > 0)

    scope_levels = [_get_scope_level(l) for l in clause]
    sorted_tuples = list(zip(scope_levels, map(abs, clause), clause))
    sorted_tuples.sort()
    sorted_clause = [t[2] for t in sorted_tuples]
    
    assert(len(sorted_clause) == len(clause))

    return sorted_clause

def _get_num_variables(quantifier):
    """
    _get_num_variables(quantifier : UNIVERSAL or EXISTENTIAL)

    Returns number of variables bound by given quantifier.
    """
    global _qcache

    return len(_qcache[quantifier][USED]) + \
           len(_qcache[quantifier][UNUSED])

def _update_occs_cnt(var, cnt):
    """
    _update_occs_cnt(var : int,
                     cnt : int)

    Updates the occurence counters of given variable by cnt (which may be
    negative or positive).
    """
    global _vcache

    _vcache[var][2] += cnt
    if _vcache[var][2] == 0:
        _qcache[_get_quantifier(var)][UNUSED].append(var)

def _generate_quantsets(num_vars, num_qsets, ratio):
    """
    _generate_quantsets(num_vars  : int,
                        num_qsets : int,
                        ratio     : float)

    return (quantsets : list)

    Generates a list of random quantifier sets according to given arguments 
    returns it.

    Returns the list of generated quantifier sets.
    """
    global _qcache, _vcache, _options

    quantsets = []
    quantifiers = [UNIVERSAL, EXISTENTIAL]
    num_sets = {EXISTENTIAL : 0, UNIVERSAL: 0}
    _num_vars = {EXISTENTIAL : 0, UNIVERSAL : 0}
    rem_vars = {EXISTENTIAL : 0, UNIVERSAL : 0}

    # prevent universal quantset at innermost scope, would be removed anyway
    # by applying forall reduction
    if _options.reduce:
        # number of quantifier sets is even -> start with UNIVERSAL
        # otherwise with EXISTENTIAL
        qindex = num_qsets % 2

    else:
        qindex = random.randint(0, 1)
        # special case
        if ratio != None:
            # if all variables have to be universal -> only one universal 
            # quantifier set exists
            if ratio == 0.0:
                qindex = 0
            # if all variables have to be existential -> only one existential
            # quantifier set exists
            elif ratio == 1.0:
                qindex = 1
        
    # if only one quantifier set is given, change ratio in order to have only
    # existential or universal variables
    if num_qsets == 1:
       if qindex == 1:
           ratio = 1.0
       else:
           ratio = 0.0

    # calculate number of existential and universal quantifier sets
    if num_qsets % 2 == 0: # even number of quantifier sets
        num_sets[EXISTENTIAL] = num_sets[UNIVERSAL] = num_qsets / 2
    else:
        if quantifiers[qindex] == EXISTENTIAL:
            num_sets[EXISTENTIAL] = math.floor(num_qsets / 2) + 1
            num_sets[UNIVERSAL] = num_sets[EXISTENTIAL] - 1
        else:
            num_sets[UNIVERSAL] = math.floor(num_qsets / 2) + 1
            num_sets[EXISTENTIAL] = num_sets[UNIVERSAL] - 1

    assert(num_sets[EXISTENTIAL] > 0 or num_sets[UNIVERSAL] > 0)
    assert(num_sets[EXISTENTIAL] + num_sets[UNIVERSAL] == num_qsets)

    # calculate number of existential and universal variables
    if ratio != None:
        if ratio > 0.0 and ratio < 1.0:
            # there has to be at least 1 existential variable if given ratio is
            # greater 0.0 and less than 1.0
            _num_vars[EXISTENTIAL] = max(1, math.floor(num_vars * ratio))
        else:
            # special case: ratio is 0.0 or 1.0 -> all variables are either
            # existential or universal
            _num_vars[EXISTENTIAL] = math.floor(num_vars * ratio)
    # just use a random number of existential variables
    else:
        # we need at least num_sets[EXISTENTIAL] and at most num_sets[UNIVERSAL]
        # existential variables in order to be sure that we always have enough
        # variables for the specified amount of quantifier sets
        _num_vars[EXISTENTIAL] = random.randint(num_sets[EXISTENTIAL],
                                           num_vars - num_sets[UNIVERSAL])

    # remaining number of variables are universal
    _num_vars[UNIVERSAL] = num_vars - _num_vars[EXISTENTIAL]
    rem_vars = _num_vars.copy()

    assert(_num_vars[EXISTENTIAL] + _num_vars[UNIVERSAL] == num_vars)
    assert(num_sets[EXISTENTIAL] + num_sets[UNIVERSAL] == num_qsets)
    
    # variables not yet used in quantifier sets
    vars = [v for v in range(1, num_vars + 1)]
    
    while num_sets[EXISTENTIAL] > 0 or num_sets[UNIVERSAL] > 0:
        qset = []
        quantifier = quantifiers[qindex]

        # add quantifier to set
        qset.append(quantifier)
        
        # determine number of variables of new quantifier set
        if num_sets[quantifier] == 1:  # last quantifier set
            vars_per_qset = rem_vars[quantifier]
        else:
            vars_per_qset = random.randint(1, int(rem_vars[quantifier] / 
                                                  num_sets[quantifier]))

        rem_vars[quantifier] -= vars_per_qset
        num_sets[quantifier] -= 1

        assert(rem_vars[quantifier] >= 0)

        # add random variables to quantifier set
        for i in range(vars_per_qset):
            assert(len(vars) > 0)
            rand_index = random.randint(0, len(vars) - 1) % len(vars)
            assert(rand_index >= 0)
            assert(rand_index < len(vars))
            var = vars.pop(rand_index)
            # cache variable information (quantifier, scope level, occurrences)
            _vcache[var] = [quantifier, len(quantsets), 0]
            # mark variable as not used yet
            _qcache[quantifier][UNUSED].append(var)
            # add variable to quantifier set
            qset.append(var)

        quantsets.append(qset)
        
        # set next quantifier
        qindex = (qindex + 1) & 1

    assert(rem_vars[EXISTENTIAL] == 0)
    assert(rem_vars[UNIVERSAL] == 0)
    assert(num_sets[EXISTENTIAL] == 0)
    assert(num_sets[UNIVERSAL] == 0)
    assert(len(vars) == 0)
    assert(len(quantsets) == num_qsets)
    assert(len(_vcache) == num_vars)
    assert(len(_qcache[EXISTENTIAL][UNUSED]) + \
           len(_qcache[UNIVERSAL][UNUSED]) == num_vars)

    return quantsets


def _generate_clause(num_ex_lits, num_un_lits):
    """
    _generate_clause(num_ex_lits : int,
                     num_un_lits : int)

    return (clause : list)

    Generates a clause with num_ex_lits existential literals and num_un_lits
    universal literals. The literals are randomly chosen but unused variables
    (with occurence count == 0) are preferred. In certain cases the clause may
    contain fewer literals than specified.
    """
    global _qcache

    clause = []
    num_lits = {EXISTENTIAL : num_ex_lits, UNIVERSAL : num_un_lits}
    rem_lits = 0

    for quantifier in num_lits:
        vars = _qcache[quantifier]
        index_cache = []
        lits = num_lits[quantifier] + rem_lits
        for i in range(lits):
            if len(vars[UNUSED]) > 0:
                index = random.randint(0, len(vars[UNUSED]) - 1)
                var = vars[UNUSED].pop(index)
                # mark variable as already used
                vars[USED].append(var)
            else:
                # prevent same variable twice in a clause
                skip_quant = False
                while 1:
                    index = random.randint(0, len(vars[USED]) - 1)
                    #assert(index >= 0)
                    #assert(index < len(vars[USED]))
                    var = vars[USED][index]
                    #assert(_get_occs_cnt(var) > 0)
                    if var not in clause and -var not in clause:
                        break 
                    else:
                        # memorize already tried indices
                        if index not in index_cache:
                            index_cache.append(index)

                    # skip this quantifier since there are no more variables
                    # left to use
                    if len(index_cache) >= len(vars[USED]):
                        skip_quant = True
                        break

                # skip variables with this quantifier as there are no variables
                # left to use in this clause. try to compensate missing var
                # with variables with different quantifier
                if skip_quant:
                    rem_lits += 1
                    continue

            # increment number of occurrenes of selected variable
            _update_occs_cnt(var, 1)
                
            # negate variable with 50% propability
            if random.randint(0, 1) == 1:
                var = -var

            # add new literal to clause
            clause.append(var)

    return clause


def _generate_num_lits(num_lits, ratio):
    """
    _generate_num_lits(num_lits : int,
                       ratio    : float)

    return (num_ex_lits, num_un_lits)

    Divide num_lits into existential and universal literals. If ratio is
    specified the number of existential literals is computed with respect to
    it, otherwise it will be computed randomly.

    """

    # generate number of literals using given ratio
    if ratio != None:
        num_ex_lits = max(1, math.floor(num_lits * ratio))
    # generate random number of literals
    else:
        # compute lower bound of existential variables to ensure that 
        # num_ex_lits + num_un_lits == num_lits
        lo_bound = num_lits - _get_num_variables(UNIVERSAL)
        if lo_bound < 0:
            lo_bound = 0
        num_ex_lits = random.randint(lo_bound,
                        min(num_lits, _get_num_variables(EXISTENTIAL)))

    num_un_lits = num_lits - num_ex_lits

    return (num_ex_lits, num_un_lits)


def _generate_clauses(num_vars, num_clauses, min_lits, max_lits, ratio):
    """
    _generate_clauses(num_vars    : int,
                      num_clauses : int,
                      min_lits    : int,
                      max_lits    : int
                      ratio       : float)
    
    return (clauses : list)

    Generates a list of random clauses with a maximum number of num_clauses.
    Each clause will contain at least min_lits and at most max_lits. Further
    the number of existential variables in a clause depends on the specified
    ratio. Forall reduction is also applied by default if --no-reduce is not
    enabled. The clauses will also be sorted if _sort_literals is enabled.

    Returns the list of generated clauses.
    """ 
    global _qcache, _options

    clauses = []
    gen_clauses = 0

    while gen_clauses < num_clauses: 
        clause = []

        # determine number of literals in new clause
        if min_lits == num_vars:
            num_lits = num_vars
        else:
            num_lits = random.randint(min_lits, max_lits)

        # calculate number of existential and universal literals in clause
        (num_ex_lits, num_un_lits) = _generate_num_lits(num_lits, ratio)
        
        # add existential and universal literals to clause
        clause = _generate_clause(num_ex_lits, num_un_lits)
        assert(len(clause) > 0)

        # sort literals in scope if enabled
        if _options.sort:
            clause = _sort_by_scope(clause)
        
        # apply forall reduction if enabled
        if _options.reduce:
            _forall_reduce(clause)

        # only append if clause contains at least one literal
        if len(clause) > 0:
            if _options.allow_unit or len(clause) > 1:
                clauses.append(clause)
                gen_clauses += 1
            else:
                assert(len(clause) == 1)
                _update_occs_cnt(abs(clause[0]), -1)

    assert(len(clauses) > 0)
    assert(len(clauses) == num_clauses)

    return clauses


def _forall_reduce(clause):
    """
    _forall_reduce(clause : list)

    Applies forall reduction on given clause.
    """
    global _stat_removed_lits, _stat_total_lits
    _stat_total_lits += len(clause)
    # initial highest existential level
    highest_ex_level = -1

    # get highest existential scope level in clause
    for literal in clause:
        if _get_quantifier(literal) == EXISTENTIAL:
            scope_level = _get_scope_level(literal)

            if scope_level > highest_ex_level:
                highest_ex_level = scope_level

    # remove literals until exists quantifier is found
    for literal in clause[:]:
        if _get_quantifier(literal) == UNIVERSAL:
            if _get_scope_level(literal) > highest_ex_level:
                clause.remove(literal)
                _update_occs_cnt(abs(literal), -1)
                _stat_removed_lits += 1


def _merge_quantifier_sets(quantsets, index):
    """
    _merge_quantifier_sets(quantsets : list,
                           index     : int)

    Merges the quantifier sets at position index and index + 1 and removes 
    quantifier set at position index + 1 from the quantifier set list.
    """
    for i in range(1, len(quantsets[index + 1])): # skip quantifier
        quantsets[index].append(quantsets[index + 1][i])

    quantsets.pop(index + 1)


def _clean_up_formula(num_vars, quantsets, clauses):
    """
    _clean_up_formula(num_vars  : int,
                      quantsets : list,
                      clauses   : list)

    return (new_num_vars : int)

    Cleans up the generated formula in order to be QDIMACS compliant. All
    empty and redundant clauses as well as unused variables will be removed.
    Further, adjacent quantifier sets with equal quantifiers will be merged.

    Returns the number of remaining variables.
    """
    global _options, _qcache
    var_offs = [0 for v in range(0, num_vars + 1)]
    new_num_vars = num_vars

    # remove unused variables and calculate new values of remaining variables
    start = _start_task("removing unused variables and quantsets...\t")
    rem_vars = 0
    rem_sets = 0
    for var in range(1, num_vars + 1):
        # found unused variable
        if _get_occs_cnt(var) == 0:
            assert(var in _qcache[_get_quantifier(var)][UNUSED])
            new_num_vars -= 1
            rem_vars += 1
            # calculate offset
            for i in range(var + 1, num_vars + 1):
                var_offs[i] += 1
            # remove unused variables from quantsets
            for qset in quantsets[:]:
                if var in qset:
                    qset.remove(var)

    # remove empty quantifier sets
    for qset in quantsets[:]:
        if len(qset) == 1:
            quantsets.remove(qset)
            rem_sets += 1
    _end_task(start)

    if _options.verbose:
        _print_info("{0:d} unused variables removed".format(rem_vars))
        _print_info("{0:d} unused quantifier sets removed".format(rem_sets))

    # merge not alternating quantifier sets if quantifier sets have been 
    # removed
    if rem_sets > 0:
        start = _start_task("merging not alternating quantifiers sets...\t")
        i = 0
        merged_sets = 0
        while i < len(quantsets) - 1:
            # check for equal quantier sets
            if quantsets[i][0] == quantsets[i + 1][0]:
                _merge_quantifier_sets(quantsets, i)
                merged_sets += 1
            else:
                i += 1
        _end_task(start)

        if _options.verbose:
            _print_info("{0:d} quantifier sets merged".format(merged_sets))

    # update variable values in all quantifier sets
    start = _start_task("updating variables in quantifier sets...\t")
    for qset in quantsets:
        for i in range(1, len(qset)):
            qset[i] -= var_offs[abs(qset[i])]
    _end_task(start)

    # update literal values in all clauses
    start = _start_task("updating literal values in clauses...\t\t")
    for clause in clauses:
        for i in range(len(clause)):
            if clause[i] < 0:
                clause[i] += var_offs[abs(clause[i])]
            else:
                clause[i] -= var_offs[abs(clause[i])]
    _end_task(start)
    
    # remove redundant clauses
    start = _start_task("removing redundant clauses...\t\t\t")
    clause_cache = {}
    red_clauses = 0
    for clause in clauses[:]:
        assert(len(clause) > 0)
        key = _hash_clause(clause)
        if key in clause_cache:
            clauses.remove(clause)
            red_clauses += 1
        else:
            clause_cache[key] = 1
    _end_task(start)

    if _options.verbose:
        _print_info("{0:d} redundant clauses removed".format(red_clauses))

    return new_num_vars

def _hash_clause(clause):
    """
    _hash_clause(clause : list)

    return (key : string)

    Creates a unique hash string of the given clause. It is used to identify
    redundant clauses.

    Returns the hash value of the given clause.
    """
    key = ""
    sorted_clause = clause[:]
    sorted_clause.sort()
    for literal in sorted_clause:
        key += ".{0:d}".format(literal)
    return key


def qbfuzz_main():
    """
    qbfuzz_main()
       
    Main function of QBFuzz. Parse arguments and generate QBF formula using
    given arguments.
    """
    global _options

    comments = []
    quantsets = []
    clauses = []

    # initialize and check parameters
    outfile = _init(comments)

    # print parameters used for generation to stderr
    if _options.verbose:
        print("\n./{0:s}".format(comments[1]), file=sys.stderr)

    # generate quantifier sets
    start = _start_task("generating quantifier sets...\t\t\t")
    quantsets = _generate_quantsets(_options.num_vars, _options.num_qsets, \
                                    _options.ratio)
    _end_task(start)

    # generate clauses
    start = _start_task("generating clauses...\t\t\t\t")
    clauses = _generate_clauses(_options.num_vars, _options.num_clauses, \
                                _options.min_lits, _options.max_lits, \
                                _options.ratio)
    _end_task(start)
    
    if _options.verbose and _options.reduce:
        _print_info("{0:.2%} literals removed by forall reduction"\
                     .format(_stat_removed_lits / _stat_total_lits))

    # create free variables by removing them from random quantifier sets
    if _options.free_ratio != None:
        num_free_vars = max(1, 
                            math.floor(_options.num_vars * _options.free_ratio))
        while num_free_vars > 0:
            qindex = random.randint(0, len(quantsets) - 1)
            # check if quantifier set contains at least one variable
            if len(quantsets[qindex]) > 1:
                vindex = random.randint(1, len(quantsets[qindex]) - 1)
                quantsets[qindex].pop(vindex)
                num_free_vars -= 1

    # clean up after modifying formula
    if _options.reduce or not _options.allow_unit or \
       _options.free_ratio != None:
        # save new number of variables (unused variables may be removed)
        _options.num_vars = _clean_up_formula(_options.num_vars, quantsets, \
                                              clauses)

    # write formula to output file
    start = _start_task("writing to output file...\t\t\t")
    _write_file(outfile, comments, _options.num_vars, quantsets, clauses)
    _end_task(start)

    if _options.verbose:
        print("\n", file=sys.stderr)

def _start_task(msg):
    """
    _start_task(msg : string)

    return (time : int)

    Prints message and start timer for a task.

    Returns 0 if verbose is disabled otherwise the start time of the task.
    """
    global _options

    if _options.verbose:
        print("\n\033[1;32m*\033[0;39m {0:s}".format(msg), end='',\
              file=sys.stderr)
        sys.stderr.flush()
        return time.time() * 1000
    
    return 0

def _end_task(start):
    """
    _end_task(start : int)

    Prints amount of time used by specific task.
    """
    if start > 0:
        print("[\033[1;32mdone\033[0;39m] {0:8.2f}ms"\
              .format(time.time() * 1000 - start), end='', file=sys.stderr)

def _print_info(msg):
    """
    _print_info(msg : string)

    Prints given message as information to last task.
    """
    print("\n    {0:s}".format(msg), end='', file=sys.stderr)

if __name__ == "__main__":
    """ QBFuzz main progam. """

    try:
        qbfuzz_main()
        sys.exit(0)
    except KeyboardInterrupt as err_msg:
        sys.exit(err_msg)

