---
title: JML Tutorial - Specifications in Method Bodies
---

The basic unit of specification and verification in JML is the method,
which has a specification outside of the body of the method.
To verify a method, OpenJML compares the method's body against its specification. 

However, it is also possible to write statements inside a method body to 
help prove that the body meets the method's specification.
Such statements can also be helpful in documenting
a method's body in a machine-checked way.
On the other hand, such specification statements are not
part of the method's specification -- for example, they are not visible to 
calling methods.

The most common such specification statements are `assert` and `assume`;
also common are specifications to aid the verification of [loops](Loops).
In addition, JML includes [ghost declarations and statements](Ghost),
which can be used to supplement other specification statements.
