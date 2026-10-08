---
title: JML Tutorial - Exercises - Multiple Method Behavior
---
# Multiple Method Behavior Exercises:
## [Multiple Method Behavior Tutorial](https://www.openjml.org/tutorial/MultipleBehaviors)

## **Question 1**
**Write the strongest specification for the code below that is needed to verify the method below? (Do not change the code, only write a specification.)**
```Java
    public int mean(int sum, int totalNum) {
        if(totalNum == 0) {
            throw new ArithmeticException();
        }
        return sum/totalNum;  // ERROR: possible overflow!
    }
```

(The possible overflow would happen when `sum` is `Integer.MIN_VALUE` and `totalNum` is -1, since there is no positive equivalent to `Integer.MIN_VALUE` in the type `int`.)

## **Question 2**
**Consider the following class. Without changing the code, write a specification for the method `max` with multiple specification cases so that the method `testMax` verifies. (Do not change any of the code of either method.)**

```Java
{% include_relative IntMax.java %}
```

**Learning Objectives:**
+ Gain more experience identifying multiple method behaviors 
+ Understand how to use the `also` clause
+ Understand the difference between `normal_behavior` and `exceptional_behavior`

## [Answer Key](MultMethodBehaviorExKey.md)

## **Resources:**
+ [Question 1 Java](MultMethodBehaviorEx1.java)
+ [Question 2 Java](IntMax.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
