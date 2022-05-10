---
title: JML Tutorial - Exercises - Specifying Loops
---
# Specifying Loops Exercises Key:
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
**Asnwer and Explanation:**
First let's understand what the code is doing. The function `reverseWord()` takes  in a `String str1` and will create a new `char[] sr2` array to store the reversal of the string passed in. We reverse the word by use of a for-loop that goes until `str1.length()` and will store the right-most character to the char array every time. Finally, we create a `String res` which will store the char array `str2` and return `res`. 

So first let's identify any pre and postconditions needed to verify the function. First, we should ensure that after the function is called the result is equal to `str1[str1.length()-1-j]` for `j` greater than or equal to zero, and less than or equal to `str1.length()-1`. Additionally, since the function is preforming a simple reversal the resulting string should be of the same length as the string passed in. Additionally, since the function is not modifying any memory locations we can say that it is pure. Let's add these conditions and then tackle the for-loop.
```Java
//@ ensures \result.length() == str1.length();
//@ ensures (\forall int j; 
//@			0 <= j <= str1.length()-1; 
//@			\result.charAt(j) == str1.charAt(str1.length()-j-1));
//@ pure
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
Now, in regards to the for-loop what do we know typically needs to specified for verifying a loop? (1) A loop invariant that puts a constraint on the range of the index; (2) check that what we expect to happen after an iteration of the loop is being accomplished - also given by a loop invariant; (3) a loop frame condition that says what memory locations have been modified by any iteration; (4) a termination condition of type integer.
 
So let's start with the first loop invariant condition: our loops using `int i` to iterate through our string so we have to include the constraints on `i`. We want `i` to run from 0 to the length, inclusive, as at the end of the loop `i` will equal the length and therefore if we don't include it in our constraints OpenJML cannot verify the loop. Second, after each iteration of the loop we want `str2[i]` to equal the kth character in `str1` - this statement is quite similar to our first ensures clause so let's use that as a base. 

We want to check for all `int j` (0 <= `j` < `i`) that `str2[j] == str1.charAt(length-1-j)`. Note that this is a helpful way to come up with your second loop invariant, by using the ensures clause of your program. Now we determine any memory locations being modified, which in this case is `str2[*]` after each iteration. 

Finally, our termination condition will simply be for as the length is decreasing (length-1)-i. So we can write the following:
```Java
//@ ensures \result.length() == str1.length();
//@ ensures (\forall int j; 
//@			0 <= j <= str1.length()-1; 
//@			\result.charAt(j) == str1.charAt(str1.length()-j-1));
//@ pure
public String reverseWord(String str1) {
        final int length = str1.length();
        char[] str2 = new char[length];
		
        //@ maintaining 0 <= i <= length;
        //@ maintaining (\forall int j; 
        //@				0 <= j < i; 
        //@ 			str2[j] == str1.charAt(length-1-j));
        //@ loop_assigns str2[*];
        //@ decreases (length-1)-i;		
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
**Asnwer and Explanation:**
Let’s first identify what is different with this code. Notice how the for-loop now runs from the length of our word down to zero, instead of counting up from zero to length. As such, this will change our previous specifications, but how? To begin let’s see what still applies. We koow that `res` and `str1`should still be the same length after we call our function since the function is still simply reversing `str1` and returning the result. We also know that our function is still `pure` as no memory is being altered. Now what about our `ensures` statement that checked that the word is successfully reversed? In this case we can simply reuse the same postcondition from part (a) since once the function has been called OpenJML doesn’t care how the function reversed the string, only that it did. As such we can write the following:
```Java
//@ ensures \result.length() == str1.length();
//@ ensures (\forall int j; 
//@			0 <= j <= str1.length()-1; 
//@			\result.charAt(j) == str1.charAt(str1.length()-j-1));
//@ pure
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
Now, let’s tackle the for-loop. Again, let us start by determining what our first oop invariant constraints are going to be. In this case our for-loop runs for `i` greater than or equal to zero, and is initalized to `length-1` so we know that our first loop invariant will have these same bounds. So we would say that `i` is between -1 and `length-1` - recall that our first loop invariant needs to consider the value of it after the loop is terminated, so in this case we include -1 because the loop terminates when `i = 0`. Additionally, note that we say `length-1` because if we just say `length` we will go out of bounds because the function `length()` doesn’t count from zero.

Again, to figure our what our second loop invariant condition will be let’s take a look at our postcondition. We know that for this maintain clause we can count upwards, so we will say that `j` has to be greater than zero. But what is our upper bound? In this case we are checking up to `(length-1)-i` - and we can see this is reflected in the for-loop because we access the index of `str2` at `(length-1)-i` when adding characters. That being said, we know that `str[j]` should equal `str1` at `(length-1)-j`. 

In this version the memory of `str2` is still be modified, so we still include that the loop assigns `str2[*]`. And as for our termination condition, we simply say `i+1`. Putting that all together we get the following:
```Java
//@ ensures \result.length() == str1.length();
//@ ensures (\forall int j; 
//@			0 <= j <= str1.length()-1; 
//@			\result.charAt(j) == str1.charAt(str1.length()-j-1));
//@ pure
public String reverseWord(String str1) {
	final int length = str1.length();
        char str2[] = new char[length];
		
        //@ maintaining -1 <= i <= length-1;
        //@ maintaining (\forall int j; 
        //@				0 <= j < (length-1)-i; 
        //@				str2[j] == str1.charAt(length-1-j));
        //@ loop_assigns str2[*];
        //@ decreases i+1;		
        for(int i = length-1; 0 <= i; i--) {
            str2[(length-1)-i] = str1.charAt(i);
        }
        String res = new String(str2);
        return res;
}
```
**Learning Objective:** 
The goal of this exercise is to give the student more experience with writing specification for loops as it can be somewhat confusing at first. For part (a) we want the student to write not only the specifications for the loop for this example, but also the pre and post conditions as the student should recognize that writing these are helpful when writing specifications for loops. We want the student to become more comfortable with writing these specifications and understand the basic format every time so that when it comes to more complicated programs they won't feel as lost when it comes to having nested loops. We want to check that the student understands what our constraints on our variable `i` are, then if they can identify what the loop should accomplish after every iteration, what is being modified, and what will make the loop terminate. If the student can determine these four specifications they should have a good idea how to start writing loop specifications with less problems. As such, part (b) checks if the student can see how the same pre and postconditions can be resued for a different version of the program, and checks if the student can identify what new loop specifications are needed. This part is a little more complex as it tasks the student with thinking about the loop backwards. 

## **Resources:**
+ [Specifying Loops Exercises](SpecifyingLoopsEx.md)
+ [Question 1 part (a) Java](SpecifyingLoopsExample1a.java)
+ [Question 1 part (b) Java](SpecifyingLoopsExample1b.java)
