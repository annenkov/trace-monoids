# Trace monoids in Cubical Agda

The trace monoid is a free partially commutative monoid (not to be confused with **partial** commutative monoids), meaning that some (but not all) letters in strings are allowed to commute.
Which letter can commute depends on an independency relation (irreflexive, symmetric). 
This relation induces an equivalence relation on strings which partitions them into equivalence classes up to commuting letters.
E.g. `aabcc` and `abacc` belong to the same equivalence class if the letters `a` and `b` are independent.

One interesting application of trace monoids is semantics of concurrency, where traces concisely capture all possible interleaving given by the independency relation.

# Why Cubical Agda

In Cubical Agda, one can define such a monoid with partial commutation using HITs.
In this case traces with commuting letters are just equal, which simplifies equational reasoning.

# The project

The project explores the ways to define trace monoids and how it can be applied to reasoning about database transaction schedules.

As an example, we consider a simple language with read and write instructions along with some arithmetic operations.
We define the notion of a serializable schedule and show how equational reasoning can be used to prove that a given schedule is serializable.
