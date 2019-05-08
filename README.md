[![Codacy Badge](https://api.codacy.com/project/badge/Grade/bfd02d3e1f7540d0ac920e4812bef953)](https://www.codacy.com/app/MarkusRabe/cadet?utm_source=github.com&utm_medium=referral&utm_content=MarkusRabe/cadet&utm_campaign=badger)
[![Build Status](https://travis-ci.org/MarkusRabe/cadet.svg?branch=master)](https://travis-ci.org/MarkusRabe/cadet)

# CADET

CADET is a solver for _quantified Boolean formulas_ with a forall-exists quantifier alternation (2QBF). The solver is based on the _Incremental Determinization_ algorithm published in SAT 2016 was written by [Markus N. Rabe](https://people.eecs.berkeley.edu/~rabe/). As of 2018, CADET is one of the fastest and most reliable solvers for 2QBF formulas. It won second price in the 2QBF track of [QBFEval](http://www.qbflib.org/qbfeval17.php) and can also _prove_ its results little overhead, which is unique in the current landscape of QBF solvers. 

## Example

Here we discuss how to encode the formula ∀ x1 x2:  ∃ y:  y = (x1 & x2) and how to interpret CADET's results.

Natively, CADET reads the [QDIMACS](http://www.qbflib.org/qdimacs.html) format (and will soon also support [QAIGER](https://github.com/ltentrup/QAIGER)). The example formula looks as follows in QDIMACS:

```qdimacs
c This QDIMACS file encodes the formula     
c forall x1, x2 exists y. y <-> x1 & x2.
c x1 is represented by number 1
c x2 is represented by number 2
c y  is represented by number 3
p cnf 3 3                                   
a 1 2 0                                     
e 3 0                                       
1 -3 0                                      
2 -3 0                                      
-1 -2 3 0                                   
```

Lines starting with `c` are comments. The _header_ is the line starting with `p cnf` followed by two numbers indicating the number of variables and the number of clauses. The lines starting with `a` and `e` are quantifiers introducing universally quantified variables 1 and 2, and the existentially quantified variable 3. The remaining three lines each state one constraint (a clause). The last line, for example states that 1 must be false or 2 must be false or 3 must be true. It is easy to check that the three constraints (clauses) together require y to be the conjunction of x1 and x2: Simply interpret the clauses as implications -x1 -> -y, -x2 -> -y, and (x1 & x2) -> y.

CADET will solve this file easily:

```bash
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


```bash
$ ./cadet -c result.aig formula.qdimacs
```

The result is written to the file `result.aig`, which is typically a bit bloated and it is intended to be minimized after generation. For example, you can use the following command to minimize circuits with [ABC](https://people.eecs.berkeley.edu/~alanmi/abc/):

```bash
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


CADET can be built from source with both clang and gcc. You can find pre-built binaries of CADET for Linux and OSX. The testing scripts require Python 3. 


To compile the solver type:

```bash
$ ./configure && make
```

To make sure the solver works correctly execute the test suite:

```bash
$ make test
```

One of the test cases will timeout as part of the testsuite and a number of tests will return with the result UNKNOWN, which is intended. 


## Usage

The most common use case for the solver is to solve formulas specified as a [QDIMACS](http://www.qbflib.org/qdimacs.html) file. 

```bash
$ ./cadet file.qdimacs
```

You can also pipe QDIMACS into the solver:

```bash
$ cat file.qdimacs | ./cadet
```

#### Input Formats

CADET reads files in both [QDIMACS](http://www.qbflib.org/qdimacs.html) and [QAIGER](https://github.com/ltentrup/QAIGER) format. Files can be zipped with gzip, but must then end with the file extension gz or gzip. 


## Proofs

CADET is able to prove (or _certify_) its results. As 2QBF formulas in QDIMACS have a forall-exists quantifier alternation, proofs for UNSAT results are given as an assignment to the universally quantified variables. Proofs for SAT results are given as a circuit, mapping assignments to the universally quantified variables to assignments to the existentially quantified variables. 

Certificates for UNSAT results are written to stdout according to the [QDIMACS](http://www.qbflib.org/qdimacs.html) standard. To print output according to the QDIMACS standard, use the `--qdimacs_out` flag. CADET checks UNSAT certificates internally by default. 

With the command line option `-c [file]` CADET writes the SAT certificate for true 2QBF. You can either specify a file name to which the certificate should be written (ending in `.aag` or `.aig`) or you can specify `sdtout` to let CADET print the certificate on the terminal. For example, type:

```bash
$ ./cadet -c certificate.aag file.qdimacs
```

As soon as you work with certificates you may want to install the [AIGER tool set](http://fmv.jku.at/aiger/aiger-1.9.4.tar.gz) and the [ABC](https://people.eecs.berkeley.edu/~alanmi/abc/). The distribution of CADET comes with several scripts that demonstrate how to generate, simplify, and check certificates using ABC and the AIGER tool set.

#### Checking Certificates

UNSAT results are checked internally by default. You can double check them by asserting the assignment to the universals in the CNF of the QDIMACS and querying a SAT solver. 

For checking SAT certificates you have two options: By default CADET produces certificates that can be checked by Certcheck, which was written by [Leander Tentrup](https://www.react.uni-saarland.de/people/tentrup.html). Certcheck comes with the distribution of [CAQE](https://www.react.uni-saarland.de/tools/caqe/). To produce certificates that are compatible with [QBFcert](http://fmv.jku.at/qbfcert/) add `--qbfcert` option to the command line. 

Note that QBFcert standard is only compatible with the ASCII format of the AIGER standard, so be sure that the certificate file name ends with `.aag`. Also, be aware that QBFcert certificates cannot be minimized by ABC. 

## Publications

[Learning Heuristics for 2QBF through Deep Reinforcement Learning](https://arxiv.org/abs/1807.08058). Gil Lederman, Markus N. Rabe, Edward A. Lee, Sanjit A. Seshia. arXiv preprint, 2018.

[Understanding and Extending Incremental Determinization for 2QBF](https://people.eecs.berkeley.edu/~sseshia/pubdir/id-cav18.pdf). Markus N. Rabe, Leander Tentrup, Cameron Rasmussen, and Sanjit Seshia. CAV, 2018.

[Encodings of Bounded Synthesis](https://www.react.uni-saarland.de/publications/FFRT17.html) Faymonville, Finkbeiner, Rabe, Tentrup. TACAS, 2017.

[Incremental Determinization](https://www.eecs.berkeley.edu/~rabe/IncrementalDeterminizationSAT2016.pdf). Markus N. Rabe and Sanjit Seshia. SAT, 2016.

## Acknowledgements

I am indebted to my collaborators, colleagues, and friends who inspired and supported me during this project. In particular, I want to mention Leander Tentrup who contributed some code to this project. I also want to thank Armin Biere and Will Klieber for fruitful discussions about various aspects of SAT and QBF solving. I also want to thank Armando Solar-Lezama, Baruch Sterin, S. Akshay, Supratik Chakraborty, and many others who contributed benchmarks and insights into their tools. 

