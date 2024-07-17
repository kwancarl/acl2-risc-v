# ACL2 RISC-V

Simple ACL2 RISC-V model, only supporting RV32I and some M-extension instructions for now. Motivated by Jolt. Warning: work in progress.

## How to use the model

In order to use the model, one should have a working version of ACL2. Then `(ld "<filename>.lisp")` will load the events contained in `<filename>.lisp` into ACL2. 

For a demo of how to simulate a RISC-V CPU, see `demo.lisp`.

## Obtaining ACL2

See the official ACL2 [page on installing ACL2](https://www.cs.utexas.edu/~moore/acl2/v8-5/HTML/installation/installation.html). If you're running a Debian-based machine, then `apt-get install acl2` should suffice. An ACL2 version supported on the Eclipse IDE is also available (see [ACL2 Sedan or ACL2s](https://www.cs.utexas.edu/~moore/acl2/v8-5/combined-manual/index.html?topic=ACL2____ACL2-SEDAN)). The instructions for ACL2s will also contain instructions for MacOS and, in particular, there is an ACL2s brew package.

## Project structure
A dependency graph between the different files should be forthcoming. For now, inspect the "`include-book`" commands at the beginning of each file. Some useful summaries:

* `rv-state.lisp`: State object definition of a RISC-V machine and supporting lemmas (e.g. read-over-write, etc.)
* `rv32i.lisp`: RISC-V step function (i.e. top-level function which performs fetch-decode-execute) and instruction correctness theorems
* `<>-instr.lisp`: semantic functions for instructions, including theorems about their assembly / dissasembly.
* `constraints.lisp`: Jolt constraints
* `mle64.lisp`: correctness theorems for Jolt instructions

## Misc. details

ACL2 should be able to verify all the files but attempting to "certify" will likely lead to failure for now.

The RISC-V specification intends a byte-addressable memory model. Many existing RISC-V models used in various zkVM efforts use a word-addressable memory model because the RISC-V instructions are standardized to 32-bits. 

Some previous machine models in the "operational semantics" tradition mix the fetch, decode, and execute steps in various functions, i.e. a single function may do some decoding and executing, making theorems about a single cycle dependent entirely on unwinding a single very complicated function. A slight novelty in this model is that we offload all the decoding into a decoding specific "layer" of functions and then prove all the relevant assembly / dissasmbly theorems for each RISC-V instruction. It is much easier to prove theorems about pure machine code / bitvectors without the burden of a clunky CPU structure. Similarly, it is much easier to prove theorems about a pure CPU structure without having to worry about bitwiddling. Connecting the two layers enables us to prove the desired theorems about the full fetch-decode-execute cycle by reducing to theorems already proven about the individual layers. The upshot of this is that we now have a verified (with respect to a cycle of the RISC-V CPU) assembler function for each RISC-V instruction, the proofs for which are entirely automatic.

The fundamental RISC-V state object `rv32` is defined using `stobj`s. According to the RISC-V specification, a 32-bit RISC-V model should have 2<sup>32</sup> addressable bytes of memory. Thus, when instantiating a concrete `rv32` state object, ACL2 will attempt to allocate ~4GB of memory, which may cause problems depending on your system. To avoid explicity allocating memory until such memory is actually needed, we should use "abstract" `stobj`s ([defabsstobj](https://www.cs.utexas.edu/~moore/acl2/v8-5/combined-manual/index.html?topic=ACL2____DEFABSSTOBJ)), similar to how [bigmem](https://www.cs.utexas.edu/~moore/acl2/v8-5/combined-manual/index.html?topic=BIGMEM____BIGMEM) is implemented. This should be supported in the future. 

The "`init`" function in `demo.lisp` avoids the memory issues above by simulating a RISC-V process using update / access functions without explicitly creating a stobj. These functions are the same used in the verification of various RISC-V components so no "soundness" is lost, even when using the "hacked" init functions. The init function should be amended once the memory issues mentioned above are resolved.

## Useful links

[ACL2 Homepage](https://www.cs.utexas.edu/~moore/acl2/)

[ACL2 Documentation](https://www.cs.utexas.edu/~moore/acl2/v8-5/combined-manual/index.html?topic=ACL2____TOP): relevant "doc" topics include `stobj`, `GL`, `bitops`, `ihs`, `x86isa`.

[ACL2 GitHub](https://github.com/acl2/acl2)

[RISC-V Specification](https://riscv.org/technical/specifications/)

[Jolt](https://jolt.a16zcrypto.com/)
