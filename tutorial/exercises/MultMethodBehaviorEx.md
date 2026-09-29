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

## **Question 2**
**Consider the following class. Without changing the code, write a specification for the method `max` with multiple specification cases so that the method `testMax` verifies. (You should not change any of the code of either method.)**
```Java
public class IntMax {
    //@ pure
    public static int max(int x, int y) {
        if (y <= x) {
            return x;
        } else {
            return y;
        }
    }

    public static void testMax() {
        int m1 = max(5, 7);
        //@ assert m1 == 7;
        int m2 = max(9, 7);
        //@ assert m2 == 9;
        int m3 = max(11,11);
        //@ assert m3 == 11;
    }
}
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
