[![Codacy Badge](https://api.codacy.com/project/badge/Grade/bfd02d3e1f7540d0ac920e4812bef953)](https://www.codacy.com/app/MarkusRabe/cadet?utm_source=github.com&utm_medium=referral&utm_content=MarkusRabe/cadet&utm_campaign=badger)
[![Build Status](https://travis-ci.org/MarkusRabe/cadet.svg?branch=master)](https://travis-ci.org/MarkusRabe/cadet)

# CADET
CADET is a solver for _quantified Boolean formulas_ with one quantifier alternation (2QBF) written and maintained by [Markus N. Rabe](https://people.eecs.berkeley.edu/~rabe/). The solver is based on the _Incremental Determinization_ algorithm published in SAT 2016. 

As of 2017, CADET is one of the fastest and most reliable solvers for 2QBF formulas. It won second price in the 2QBF track of [QBFEval](http://www.qbflib.org/qbfeval17.php). See below for an overview on installation and usage of CADET. Detailed information can be found in doc/user_guide.pdf. 


## Requirements and Compilation

CADET comes with no requirements but those included in the package. 
Any modern C compiler (clang or gcc) should be able to build CADET. 
The testing scripts require Python 2.7. 

To compile the solver type:

> ./configure && make

To make sure the solver works correctly execute the test suite:

> make test

One of the test cases will timeout as part of the testsuite and a number of tests will return with the result UNKNOWN, which is the intended result. 

## Usage

The most common use case for the solver is to solve formulas specified as a QDIMACS file. 

> ./cadet file.qdimacs

You can also pipe a QDIMACS file in the solver:

> cat file.qdimacs | ./cadet

### Input Formats

CADET reads files in both QDIMACS and AIGER format. Files can be zipped with gzip, but must then end with the file ending gz or gzip. Details on the interpretation of AIGER files as 2QBF can be found in doc/user_guide.pdf

### Certification

With the command line option `-c [file]` CADET is able to produce certificates for true 2QBF (false 2QBF are certified internally by default). You can either specify a file name to which the certificate should be written (ending in `.aag` or `.aig`) or you can specify `sdtout` to let CADET print the certificate on the terminal. These certificates represent the Skolem function that prove the given formula to be true. For example, type:

> ./cadet -c certificate.aag file.qdimacs

As soon as you work with certificates you may want to install the [AIGER tool set](http://fmv.jku.at/aiger/aiger-1.9.4.tar.gz) and the [ABC](https://people.eecs.berkeley.edu/~alanmi/abc/). The distribution of CADET comes with several scripts that demonstrate how to generate, simplify, and check certificates using ABC and the AIGER tool set.

#### Certcheck and QBFcert

By default CADET produces certificates that can be checked by Certcheck, which was written by Leander Tentrup. Certcheck comes with the distribution of [CAQE](https://www.react.uni-saarland.de/tools/caqe/). To produce certificates that are compatible with [QBFcert](\url{http://fmv.jku.at/qbfcert/}) add `--qbfcert` option to the command line. 

Note that QBFcert standard is only compatible with the ASCII format of the AIGER standard, so be sure that the certificate file name ends with `.aag`. Also, be aware that QBFcert certificates cannot be minimized by ABC. 

