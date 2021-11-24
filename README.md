# Trace monoids in Cubical Agda

The trace monoid is a free partially commutative monoid (not to be confused with **partial** commutative monoids), meaning that some (but not all) letters in strings are allowed to commute.
Which letter can commute depends on an independency relation (irreflexive, symmetric). 
This relation induces an equivalence relation on strings which partitions them into equivalence classes up to commuting letters.
E.g. `aabcc` and `abacc` belong to the same equivalence class if the letters `a` and `b` are independent.

One interesting application of trace monoids is semantics of concurrency, where traces concisely capture all possible interleavings given by the independency relation.

# Why Cubical Agda

In Cubical Agda, one can define such a free monoid with partial commutation using HITs.
In this case, traces with commuting letters are just equal, which simplifies equational reasoning.

# The project

The project explores how to define a trace monoid and how it can be applied to reasoning about database transaction schedules.

As an example, we consider a simple language with `read` and `write` instructions, along with some arithmetic operations.
We define the notion of a serializable schedule and show how equational reasoning can be used to prove that a given schedule is serializable.
The use of HITs allows for synthetic reasoning about execution traces up to permutations of independent actions.
It's synthetic in the sense that one doesn't have to reason about permutations (or interleavings) of actions explicitly.

We demonstrate further that the reasoning on traces is sound wrt. store semantics for a read-write language of schedules.
The proof methodology is again driven by commuting actions: we define store semantics on traces using the elimination principle for the trace monoid.
The elimination principle requires that the commuting action in the trace are respected by the semantic function.
This gives us a nice (and idiomatic) way of structuring the soundness proof.
