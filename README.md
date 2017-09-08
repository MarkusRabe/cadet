# CADET
A QBF solver based on the paper "Incremental Determinization" published in SAT 2016. 

See doc/user_guide.pdf for detailed information on compilation and usage. 



## Requirements

CADET comes with no requirements but those included in the package. 
Any modern C compiler (clang or gcc) should be able to build CADET. 
The testing scripts require Python 2.7. 


## Compilation

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

