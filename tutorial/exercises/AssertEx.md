---
title: JML Tutorial - Exercises - ...
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

# Assert Statements Exercises:
## **Question 1**
**Given three integers, write a function that finds which is the largest of the three. Determine the specifications needed to verify the function.**

## **Question 2**
**Given the function below, what assertions can be concluded?**
```Java
public boolean primeChecker(int num) {
	boolean flag;
	for (int i = 2; i <= num / 2; i++) {
		if (num % i == 0) {
			flag = false;
			//first assertion here
			//second assertion here 
			return flag;
		}
	}
	
	flag = true;
	//third assertion here
	return flag;
}
```
## **[Key](AssertExKey.md)**
