# PTX Memory Consistency Model

Daniel Lustig, Sameer Sahasrabuddhe, and Olivier Giroux, "A Formal Analysis of the NVIDIA PTX Memory Consistency Model", in _Proceedings of the 24th ACM International Conference on Architectural Support for Programming Languages and Operating Systems (ASPLOS ’19)_, April 13–17, 2019, Providence, RI, USA.

[Paper](PTXMemoryModelASPLOS2019.pdf)


# Instructions

To run:
- Put Coq 8.4pl6 in your path
- Put javac into your path
- Run "make"
- Success!


# Questions/Comments/Feedback

This is research-quality software built in support of our ASPLOS paper.
If you have questions, are interested in using this infrastucture, want to extend the code for your own purposes, etc., please feel free to reach out to Dan Lustig, dlustig@nvidia.com


# Makefile targets

all: build the proofs
clean: clean up compiled files
src11_4: test the RC11 -> PTX mapping empirically using Alloy, with a bound of 4
src11_5: test the RC11 -> PTX mapping empirically using Alloy, with a bound of 5


# File listing:

## alloqc infrastructure:

* alloy4.2.jar: Alloy itself, from http://alloy.mit.edu/alloy/downloads/alloy4.2.jar, but very lightly modified to improve compiler compatibility
* RunAlloy.java: a small wrapper to run Alloy from the command line
* Alloqc.java: the Alloy-Coq compiler source
* alloqc.sh: a helper script to run alloqc
* Makefile: to build alloqc, compile the alloy file, and then check the proofs with Coq

## Alloy files

* util.als: generic Alloy helper functions
* ptx.als: the definition of the PTX memory model
* src11.als: the definition of the Scoped RC11 memory model (derived from [30], as described in paper)
* compile_src11_ptx.als: the mapping from Scoped RC11 to PTX

# Coq files

* alloy.v: a Coq model of Alloy logic
* alloy_util.v: a library of common helper functions
* case.v: a library for structuring proofs, derived from common online material
* src11_ptx.v: the proofs of correctness
* compile_src11_ptx.v: the auto-generated Coq file produced by alloqc, included here for convenience, if you don't want to build Alloqc
