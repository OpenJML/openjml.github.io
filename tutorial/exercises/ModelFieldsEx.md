---
title: JML Tutorial - Exercises - Model Fields and Datagroups
---
# Exercises:
## [Tutorial](https://www.openjml.org/tutorial/ModelFields)

## **Question 1**
**As an exercise, change the specification of the class [Polygon](https://www.openjml.org/tutorial/Polygon.java) in the tutorial to enforce the public invariant that the longest side should always have a strictly positive value. (Note that `1/2` is 0 in Java.) Check your work by using openjml to verify the correctness of the result.**

## **Question 2**
**Correctly implement the following interface using a concrete class, say `MultipleViewPointImpl`, but only using two `double` fields. Recall that (in 2 dimensions) the x coordinate of a point is given by the equation `x = radius * cos(angle)` and the y coordinate is given by the equation `y = radius * sin(angle)`. In the other direction the radius is given by `radius = sqrt(x*x + y*y)` and the angle is given by `angle = atan2(y,x)`. (These formulas are from [Wikipedia](https://en.wikipedia.org/wiki/Polar_coordinate_system). Note that both `sqrt` and `atan2` are static methods that are provided by `java.lang.Math`.)**

## **[Answer Key](ModelFieldsExKey)**

## Resources
+ [Polygon file](https://www.openjml.org/tutorial/Polygon.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)



