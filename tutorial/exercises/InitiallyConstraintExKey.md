---
title: JML Tutorial - Exercises - Minimizing replicated specifications (initially, constraint, invariant clauses)
---
# Exercises
## [Minimizing replicated specifications Tutorial](https://www.openjml.org/tutorial/InitiallyConstraint)

## **Question 1**
The following is one way to answer this question.

```
{% include_relative InchesAns.java %}
```

Note that the above uses two `initially` clauses, this is equivalent to conjoining the first to the second using `&&`.

## **Question 2**
The following is one way to answer this question.

```
{% include_relative LogAns.java %}
```

Depending on the version of OpenJML used, this may still not verify, because some of the operations on the built-in type `String` may not have been implemented yet in the tool.

## Resources
+ [All exercises](exercises)
