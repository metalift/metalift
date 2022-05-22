---
sidebar_position: 1
---

# Solving a Synthesis Problem
Before we dive into an end-to-end verified lifting application, let's familiarize ourselves with the basic concepts in Metalift with a synthesis problem.

Let us synthesize a function $f(x)$ such that for all integer $x$, $f(x) \geq 0$ and $f(x) \geq x$. Formally, we want to solve the following problem: $\exists{f}. \forall x \in \mathbb{N}. f(x) \geq 0 \wedge f(x) \geq x$. The $\forall$ **universal quantifier** is so key to verification that it's in our logo!

## Define the Verification Conditions
The first step to encoding this with Metalift is to define the conditions that we want to verify. These conditions can be specified using the __Metalift IR__, which includes a variety of common operations on types like booleans, integers, lists, and sets that Metalift knows the meaning of.

First, we import the IR package as well as the Metalift types we'll be using in the verification conditions:

<!--phmdoctest-share-names-->
```python
from metalift import ir
```

Then, we define the verification conditions:

<!--phmdoctest-share-names-->
```python
x = ir.Var("x", ir.Int())

correct = ir.And(
  # f(x) >= 0
  ir.Ge(
    ir.Call(
      'f', # function name
      ir.Int(), # return type
      x # arguments
    ),
    ir.IntLit(0)
  ),
  # f(x) >= x
  ir.Ge(
    ir.Call('f', ir.Int(), x),
    x
  )
)
```

## Create a Program Grammar
TODO

## Synthesize!
TODO
