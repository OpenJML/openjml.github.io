---
title: JML Tutorial - Exercises - Multiple Method Behavior
---
# Multiple Method Behavior Exercises:
## [Multiple Method Behavior Tutorial](https://www.openjml.org/tutorial/MultipleBehaviors)

## **Question 1**
**Write the strongest specification for the code below that is needed to verify the function below? (Do not change the code, only write a specification.)**
```Java
public int mean(int sum, int totalNum) {
    if(totalNum == 0) {
        throw new ArithmeticException();
    }
    return sum/totalNum;
}
```
**Learning Objectives:**
+ Gain more experience identifying multiple method behaviors 
+ Understand how to use the `also` clause
+ Understand the difference between `normal_behavior` and `exceptional_behavior`

## [Answer Key](MultMethodBehaviorExKey.md)

## **Resources:**
+ [Question 1 Java](MultMethodBehaviorEx1.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
