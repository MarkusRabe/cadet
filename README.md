
# CADET

CADET is a solver for _quantified Boolean formulas_ with a forall-exists quantifier alternation (2QBF). The solver is based on the _Incremental Determinization_ algorithm published in SAT 2016 was written by [Markus N. Rabe](https://people.eecs.berkeley.edu/~rabe/). As of 2018, CADET is one of the fastest and most reliable solvers for 2QBF formulas. It won second price in the 2QBF track of [QBFEval](http://www.qbflib.org/qbfeval17.php) and can also _prove_ its results little overhead, which is unique in the current landscape of QBF solvers. 

## Example

Here we discuss how to encode the formula ∀ x1 x2:  ∃ y:  y = (x1 & x2) and how to interpret CADET's results. 

Natively, CADET reads the [QDIMACS](http://www.qbflib.org/qdimacs.html) format (and will soon also support [QAIGER](https://github.com/ltentrup/QAIGER)). The example formula looks as follows in QDIMACS:

```qdimacs
c This QDIMACS file encodes the formula     lines starting with c are a comment
c forall x1, x2 exists y. y <-> x1 & x2.
c x1 is represented by number 1
c x2 is represented by number 2
c y  is represented by number 3
p cnf 3 3                                   header introducing 3 variables and 3 clauses
a 1 2 0                                     Introduces the universal variables 1 and 2
e 3 0                                       Introduces the existential varible 3
1 -3 0                                      A constraint stating 1 is true or 3 is false
2 -3 0                                      2 is true or 3 is false
-1 -2 3 0                                   1 is false, 2 is false, or 3 is true
```

It is easy to check that the three constraints (clauses) together require y to be the conjunction of x1 and x2: Simply interpret the clauses as implications -x1 -> -y, -x2 -> -y, and (x1 & x2) -> y.

CADET will solve this file easily:

```
$ ./cadet formula.qdimacs
```

Output:
```
Processing file "formula.qdimacs".
CADET v2.3
SAT
```

This indicates that the formula is satsifiable (i.e. true, as we consider only closed formulas).
To prove formulas true CADET constructs a function assigning a value to y for every assignment to x1 and x2 (a _Skolem function_). For many applications, such as circuit repair, safety games, and [strategy extraction for LTL synthesis](https://www.react.uni-saarland.de/publications/FFRT17.html) we are interested in the function that CADET computed as it represents the solution of the encoded problem. With the command line argument `-c <filename>` CADET outputs this function as an [AIGER](fmv.jku.at/aiger/) circuit: 

```
$ ./cadet -c result.aig formula.qdimacs
```

The result is written to the file `result.aig`, which is typically a bit bloated and it is intended to be minimized after generation. For example, you can use the following command to minimize circuits with [ABC](https://people.eecs.berkeley.edu/~alanmi/abc/):

```
$ abc -c "read result.aig; dc2; write result.aig"
```

After the minimization a circuit with a single AND-gate remains:

```aiger
aag 3 2 0 1 1
2
4
6
6 4 2
i0 1
i1 2
o0 3
```

To view a human-readable version of the circuit as shown above you have to convert the AIGER binrary formag `.aig` to the AIGER ASCII format `.aag` using the tool `aigtoaig` available in the [AIGER toolset](http://fmv.jku.at/aiger/aiger-1.9.9.tar.gz). 

## Installing CADET

[![Codacy Badge](https://api.codacy.com/project/badge/Grade/bfd02d3e1f7540d0ac920e4812bef953)](https://www.codacy.com/app/MarkusRabe/cadet?utm_source=github.com&utm_medium=referral&utm_content=MarkusRabe/cadet&utm_campaign=badger)
[![Build Status](https://travis-ci.org/MarkusRabe/cadet.svg?branch=master)](https://travis-ci.org/MarkusRabe/cadet)

CADET can be built from source with both clang and gcc. You can find pre-built binaries of CADET for Linux and OSX. The testing scripts require Python 2.7. 

To compile the solver type:

```
$ ./configure && make
```

To make sure the solver works correctly execute the test suite:

```
$ make test
```

One of the test cases will timeout as part of the testsuite and a number of tests will return with the result UNKNOWN, which is intended. 


## Usage

The most common use case for the solver is to solve formulas specified as a [QDIMACS](http://www.qbflib.org/qdimacs.html) file. 

```bash
$ ./cadet file.qdimacs
```

You can also pipe QDIMACS into the solver:

```
$ cat file.qdimacs | ./cadet
```

#### Input Formats

CADET reads files in both [QDIMACS](http://www.qbflib.org/qdimacs.html) and [AIGER](http://fmv.jku.at/papers/BiereHeljankoWieringa-FMV-TR-11-2.pdf) format. Files can be zipped with gzip, but must then end with the file extension gz or gzip. Details on the interpretation of AIGER files as 2QBF can be found in the [user guide](https://github.com/MarkusRabe/cadet/blob/master/docs/user_guide.pdf). Note that the current AIGER input is being phased out in favor of the [QAIGER](https://github.com/ltentrup/QAIGER) format, a new standard being developed in the QBF community. 

## Proofs

CADET is able to prove (or _certify_) its results. As 2QBF formulas in QDIMACS have a forall-exists quantifier alternation, proofs for UNSAT results are given as an assignment to the universally quantified variables. Proofs for SAT results are given as a circuit, mapping assignments to the universally quantified variables to assignments to the existentially quantified variables. 

Certificates for UNSAT results are written to stdout according to the [QDIMACS](http://www.qbflib.org/qdimacs.html) standard. To print output according to the QDIMACS standard, use the `--qdimacs_out` flag. CADET checks UNSAT certificates internally by default. 

With the command line option `-c [file]` CADET writes the SAT certificate for true 2QBF. You can either specify a file name to which the certificate should be written (ending in `.aag` or `.aig`) or you can specify `sdtout` to let CADET print the certificate on the terminal. For example, type:

```
$ ./cadet -c certificate.aag file.qdimacs
```

As soon as you work with certificates you may want to install the [AIGER tool set](http://fmv.jku.at/aiger/aiger-1.9.4.tar.gz) and the [ABC](https://people.eecs.berkeley.edu/~alanmi/abc/). The distribution of CADET comes with several scripts that demonstrate how to generate, simplify, and check certificates using ABC and the AIGER tool set.

#### Checking Certificates

UNSAT results are checked internally by default. You can double check them by asserting the assignment to the universals in the CNF of the QDIMACS and querying a SAT solver. 

For checking SAT certificates you have two options: By default CADET produces certificates that can be checked by Certcheck, which was written by [Leander Tentrup](https://www.react.uni-saarland.de/people/tentrup.html). Certcheck comes with the distribution of [CAQE](https://www.react.uni-saarland.de/tools/caqe/). To produce certificates that are compatible with [QBFcert](http://fmv.jku.at/qbfcert/) add `--qbfcert` option to the command line. 

Note that QBFcert standard is only compatible with the ASCII format of the AIGER standard, so be sure that the certificate file name ends with `.aag`. Also, be aware that QBFcert certificates cannot be minimized by ABC. 

## Publications

[Incremental Determinization](https://www.eecs.berkeley.edu/~rabe/IncrementalDeterminizationSAT2016.pdf). Rabe and Seshia. SAT, 2016. 

[Encodings of Bounded Synthesis](https://www.react.uni-saarland.de/publications/FFRT17.html) Faymonville, Finkbeiner, Rabe, Tentrup. TACAS, 2017.

## Acknowledgements

I am indebted to my collaborators, colleagues, and friends who inspired and supported me during this project. In particular, I want to mention Leander Tentrup who contributed some code to this project. I also want to thank Armin Biere and Will Klieber for fruitful discussions about various aspects of SAT and QBF solving. I also want to thank Armando Solar-Lezama, Baruch Sterin, S. Akshay, Supratik Chakraborty, and many others who contributed benchmarks and insights into their tools. 



