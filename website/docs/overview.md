---
sidebar_position: 0
---

# Overview
Metalift is a framework for building compilers for domain-specific languages (DSLs). If you are a developer and you want to use a new DSL for your application, you would need to rewrite your code manually, which is often tedious and error-prone. Rather than doing that, you can use Metalift to _generate a compiler_ that translates from your source language to your favorite DSL!

## How does it work?
Metalift is a compiler generator. Unlike traditional syntax-driven compilers, which consists of rules that recognize patterns in the input code and translate them into the target language, Metalift uses [verified lifting](https://homes.cs.washington.edu/~akcheung/papers/pldi16.html) to search for possible candidate programs in the target language that the given input can be
translated to. This frees you from the need to devise, check, and maintain those pesky syntax-driven rules!

To make the search efficient, rather than searching programs that are expressible in the concrete syntax of the target DSL, Metalift searches over the space of programs expressed in a high-level _specification language_ instead. The specification language has a functional language-like syntax (think Haskell) and represents the semantics of the target DSL. See [below](#specLang) for details.

The Metalift toolchain consists of three components, as shown below:
![](/img/docs/overview/arch.png)

First, the input code is parsed into an abstract syntax tree (AST), with each node in the tree representing some part of the input program (e.g., a statement, an expression, etc). After that, Metalift extracts code fragments from the input AST that are amenable for translation to the target DSL. Note that we are not aiming to do whole program transformations here. Given the target being a _domain-specific language_, it is likely that only parts of the input application is expressible using the DSL. You probably don't want to translate the entire application anyway: consider moving computation to the GPU for instance. You probably only want to move the most computationally intensive kernels to the GPU, and leave the rest of your application to remain on the CPU.

Metalift currently has a parser for input programs in LLVM IR, which can be generated from languages like C/C++ and Rust.

Each extracted code fragment is then passed to a program synthesizer (we currently use the [Rosette](https://emina.github.io/rosette/) synthesizer) which searches over the space of programs expressed in the specification language. If a candidate program can be proven to be semantically equivalent to the input (this is currently done using the [CVC5](https://cvc5.github.io) theorem prover), it is then passed over to the code generator. Otherwise, we ask the synthesizer to find another candidate until we run out of programs or it times out.

Each successfully verified candidate program is then processed by the code generator, which translates the candidate program into the concrete syntax of the DSL. The resulting DSL program is then "stitched" back into the original code, with glue code generated to call the generated DSL program as needed. This is illustrated in the diagram above.

## Technical Overview
For those who would like to get a more in-depth understanding of the concepts behind lifting, check out [this overview paper]( https://drops.dagstuhl.de/opus/volltexte/2023/18231/)!

## Prior Results
While we are still building out Metalift, our goal is to use it to reproduce the prior standalone transpilers that were constructed using verified lifting:

- [QBS (Java to SQL)](https://casper.uwplse.org/)
- [STNG (Fortran to Halide)](http://stng.uwplse.org/)
- [Dexter (C++ to Halide)](http://dexter.uwplse.org/)
- [Domino (C to a programmable switch ISA)](http://web.mit.edu/domino/)
- [Rake (Halide to Hexagon DSP)](https://github.com/uwplse/rake/)
- [Katara (sequential data types to CRDTs)](https://github.com/hydro-project/katara)

Contact us if you have other use cases!
