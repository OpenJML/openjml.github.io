---
title: JML Tutorial - Exercises - Visibility
---
# Ghost Variable Exercises:
## [Ghost Variable Tutorial](https://www.openjml.org/tutorial/Ghost)

## **Question 1**
**Suppose we want to implement integer pairs in such a way that the method `lesserValue`, which should return the element of the pair that is the least of the two integers, will be very efficient, and we are willing to trade a bit of extra space in the integer pairs for that efficiency. Then it might make sense to precompute the lesser of the two integers in the constructor, and to use ghost fields to remember which was intended to be the first field and the second field. This is the idea behind the following class. The exercise is to complete the decaration of the class by adding declarations of (public) `ghost` fields `first` and `second`, which remember which was the first and second argument to the constructor, and by setting those ghost fields to the appropriate values in the constructor.  Then ensure that the entire class verifies using OpenJML.**

```
{% include_relative IntPair.java %}
```

## **Question 2 (Advanced)**
**In the class `IntPair`, the fields `lesser`, `greater`, and `increasing` are all declared as `spec_public`. See if you can eliminate all uses of `spec_public` in a version of `IntPair` by using `model` fields and `private represents` clauses, while declaring the fields `lesser`, `greater`, and `increasing` to all be just `private` (and not `spec_public`). Hint: you will need to use invariants, but all the invariants can be public.**

**Learning Objectives:**
+ Understand how to use ghost fields and computations in specifications
+ Understand when to use ghost fields and computations.

## **[Answer Key](GhostExKey.md)**

## Resources
+ [IntPair file](IntPair.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
