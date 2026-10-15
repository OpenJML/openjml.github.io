---
title: JML Tutorial - Exercises - Nullable and non-null values and types
---
# Exercises:
## [Nullness Tutorial](https://www.openjml.org/tutorial/Nullness)

## **Question 1**
**Consider the following code, which does _not_ verify in JML.**
```Java
{% include_relative ObjPair.java %}
```

(a) **Why does the line marked as wrong in the method `test()` not verify?**

(b) **What could be done to the method `test()` to make the code verify?**

(c) **Aside from changing the method `test()`, what else could be done
    so that the program would verify?**

**Learning Objectives:**
+ Understand JML's defaults about non-null variables.
+ Understand how to fix code that has verification problems related to null.

## **[Answer Key](NullnessExKey.md)**

## **Resources:**
+ [Question 1 Java](ObjPair.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
