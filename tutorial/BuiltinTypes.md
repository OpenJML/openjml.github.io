---
title: JML Tutorial - Built-in specification types
---

When writing specifications one needs some data types in order to provide structure and abstraction. One could, and is allowed to, use classes constructed in Java for this purpose. However, they have some drawbacks:
* Java classes, even designed for specification, retain aspects of Java that make their semantics complex and difficult to mix with analyzing the target program. An example is needing specification operations to be independent of and not affect the heap.
* Specially designed, mathematical types can have simple syntax and value-based semantics that make them easy to understand and easier for logical solvers to reason about. In fact, in some cases the specification types can be mapped directly onto structures that are built-in to solvers.

One potential disadvantage of custom-designed types is that it is an additional sub-language for the JML user to use. In fact, a library of Java-based classes for specification would require the same learning hurdle. 

_The current design for JML is to define a small core set of built-in mathematical, value-oriented types with a Java-like syntax._

This lesson introduces those types, with details described in subsequent lessons; each type name is a link to a page describing that type. They are
* [`\bigint`](type-bigint) --- an type of unbounded, mathematical integers
* [`\real`](type-real) --- a type of (mathematical) real numbers
* [`\set<T>`](type-set) --- a parameterized type of finite sets of elements of type T
* [`\seq<T>`](type-seq) --- a parameterized type of finite sequences of elements of type T
* [`\map<T,U>`](type-map) --- a parameterized type of finite maps mapping keys of type T to elements of type U
* [`\string`](type-string) --- a built-in type of immutable (value-semantics) strings (sequences of the primitive Java type `char`)
* [`\range`](type-range) --- a range of \bigint values, from a lower \bigint bound up to and not including an upper \bigint bound
* [`\TYPE`](type-TYPE) --- a type for reasoning about (compile-time) types of Java expressions

The type parameter of the parameterized JML built-in types may be either a Java reference type or a JML built-in type, but not a primitive Java type. Where equality comparisons are needed among values of Java or JML types, `==` is used.
