---
title: JML Tutorial - Exercises - Multiple Method Behavior
---
# Multiple Method Behavior Exercises:
## **Question 1**
**Given the function below, determine the strongest specifications needed to verify the function below.**
```Java
public int mean(int sum, int totalNum) {
	if(totalNum == 0) throw new ArithmeticException();
		
  return sum/totalNum;
}
```
**Learning Objectives:**
+ Gain more experience identifying multiple method behaviors 
+ Understand how to use the `also` clause
+ Understand the difference between `normal_behavior` and `exceptional_behavior`

## **[Answer Key](MultMethodBehaviorExKey.md)**
