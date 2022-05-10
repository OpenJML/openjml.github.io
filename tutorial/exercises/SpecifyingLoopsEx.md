---
title: JML Tutorial - Exercises - Specifying Loops
---
# Specifying Loops Exercises:
## **Question 1**
**(a) Determine the strongest specifications needed to verify the function.**
```Java
public String reverseWord(String str1) {
        final int length = str1.length();
        char[] str2 = new char[length];
		
        for(int i = 0; i < length; i++) {
            str2[i] = str1.charAt(length-1-i);
        }
        String res = new String(str2);
        return res;
}
```
**(b) Consider the modified code below. Determine the strongest specifications for this version of the same program.**
```Java
public String reverseWord(String str1) {
        final int length = str1.length();
        char str2[] = new char[length];
		
        for(int i = length-1; 0 <= i; i--) {
            str2[(length-1)-i] = str1.charAt(i);
        }
        String res = new String(str2);
        return res;
}
```
**Learning Objectives:**
+ Understand loop invariants, and how to use `maintaining`, `loop_assigns`, and `decreases`
+ Understand how writing postconditions can be helpful to understand what our loop should be doing after every iteration
+ Understand the order to write loop specifications
+ Gain more experience with past tutorial content  

## **[Answer Key](SpecifyingLoopsExKey.md)**

