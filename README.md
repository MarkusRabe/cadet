[![Codacy Badge](https://api.codacy.com/project/badge/Grade/bfd02d3e1f7540d0ac920e4812bef953)](https://www.codacy.com/app/MarkusRabe/cadet?utm_source=github.com&utm_medium=referral&utm_content=MarkusRabe/cadet&utm_campaign=badger)
[![Build Status](https://travis-ci.org/MarkusRabe/cadet.svg?branch=master)](https://travis-ci.org/MarkusRabe/cadet)

# CADET
CADET is a solver for _quantified Boolean formulas_ with a forall-exists quantifier alternation (2QBF). The solver is based on the _Incremental Determinization_ algorithm published in SAT 2016 was written by [Markus N. Rabe](https://people.eecs.berkeley.edu/~rabe/). 

As of 2017, CADET is one of the fastest and most reliable solvers for 2QBF formulas. It won second price in the 2QBF track of [QBFEval](http://www.qbflib.org/qbfeval17.php). CADET can also _prove_ its results little overhead, which is unique in the current landscape of QBF solvers. 


## Installing CADET

CADET can be built from source with both clang and gcc. You can find pre-built binaries of CADET for Linux and OSX. The testing scripts require Python 2.7. 

To compile the solver type:

> ./configure && make

To make sure the solver works correctly execute the test suite:

> make test

One of the test cases will timeout as part of the testsuite and a number of tests will return with the result UNKNOWN, which is intended. 

## Usage

The most common use case for the solver is to solve formulas specified as a [QDIMACS](http://www.qbflib.org/qdimacs.html) file. 

> ./cadet file.qdimacs

You can also pipe QDIMACS into the solver:

> cat file.qdimacs | ./cadet

#### Input Formats

CADET reads files in both [QDIMACS](http://www.qbflib.org/qdimacs.html) and [AIGER](http://fmv.jku.at/papers/BiereHeljankoWieringa-FMV-TR-11-2.pdf) format. Files can be zipped with gzip, but must then end with the file extension gz or gzip. Details on the interpretation of AIGER files as 2QBF can be found in the [user guide](https://github.com/MarkusRabe/cadet/blob/master/doc/user_guide.pdf).

## Proofs

CADET is able to prove (or _certify_) its results. As 2QBF formulas in QDIMACS have a forall-exists quantifier alternation, proofs for UNSAT results are given as an assignment to the universally quantified variables. Proofs for SAT results are given as a circuit, mapping assignments to the universally quantified variables to assignments to the existentially quantified variables. 

Certificates for UNSAT results are written to stdout according to the [QDIMACS](http://www.qbflib.org/qdimacs.html) standard. To print output according to the QDIMACS standard, use the `--qdimacs_out` flag. CADET checks UNSAT certificates internally by default. 

With the command line option `-c [file]` CADET writes the SAT certificate for true 2QBF. You can either specify a file name to which the certificate should be written (ending in `.aag` or `.aig`) or you can specify `sdtout` to let CADET print the certificate on the terminal. For example, type:

> ./cadet -c certificate.aag file.qdimacs

As soon as you work with certificates you may want to install the [AIGER tool set](http://fmv.jku.at/aiger/aiger-1.9.4.tar.gz) and the [ABC](https://people.eecs.berkeley.edu/~alanmi/abc/). The distribution of CADET comes with several scripts that demonstrate how to generate, simplify, and check certificates using ABC and the AIGER tool set.

#### Checking Certificates

UNSAT results are checked internally by default. You can double check them by asserting the assignment to the universals in the CNF of the QDIMACS and querying a SAT solver. 

For checking SAT certificates you have two options: By default CADET produces certificates that can be checked by Certcheck, which was written by [Leander Tentrup](https://www.react.uni-saarland.de/people/tentrup.html). Certcheck comes with the distribution of [CAQE](https://www.react.uni-saarland.de/tools/caqe/). To produce certificates that are compatible with [QBFcert](http://fmv.jku.at/qbfcert/) add `--qbfcert` option to the command line. 

Note that QBFcert standard is only compatible with the ASCII format of the AIGER standard, so be sure that the certificate file name ends with `.aag`. Also, be aware that QBFcert certificates cannot be minimized by ABC. 

## Publications

[Incremental Determinization](https://www.eecs.berkeley.edu/~rabe/IncrementalDeterminizationSAT2016.pdf). Markus Rabe and Sanjit Seshia. SAT, 2016. 

## Acknowledgements

I am indebted to my collaborators, colleagues, and friends who inspired and supported me during this project. In particular, I want to mention Leander Tentrup who contributed some code to this project. I also want to thank Armin Biere and Will Klieber for fruitful discussions about various aspects of SAT and QBF solving. I also want to thank Armando Solar-Lezama, Baruch Sterin, S. Akshay, Supratik Chakraborty, and many others who contributed benchmarks and insights into their tools. 



