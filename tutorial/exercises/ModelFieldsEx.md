---
title: JML Tutorial - Exercises - Model Fields and Datagroups
---
# Exercises:
## [Tutorial](https://www.openjml.org/tutorial/ModelFields)

## **Question 1**
As an exercise, change the specification of the class [Polygon]((https://www.openjml.org/tutorial/PolygonMM.java) in the tutorial to enforce the invariant that the longest side should always have a strictly positive value. (Note that `1/2` is 0 in Java.) You may need to use `assume` statements, as the prover that openjml uses cannot prove some facts about division (due to fundamental limitations on logic). Check your work by using openjml to verify the correctness of the result.

## **[Answer Key](ModelFieldsExKey.md)**

## Resources
+ [Polygon file](https://www.openjml.org/tutorial/Polygon.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
