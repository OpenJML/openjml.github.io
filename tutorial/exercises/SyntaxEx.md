---
title: JML Tutorial - Exercises - Syntax
---
# Syntax Exercises:
## [Syntax Tutorial](https://www.openjml.org/tutorial/Syntax)

## **Question 1**
**What is wrong with the following JML-annotated Java program?**

```
public class AnnotationSyntax {

    //@requires false;
    //@ensures true;
    public static void test(/*@nonnull*/ int[] a) {
        //@assert false;
    }

    public static void main() {
        int[] arr = new int[1];
        arr[0] = 0;
        test(arr);
    }
}
```


## **Question 2**
**Why doesn't running `openjml --require-white-space` on the above code give any errors?**

## **Question 3**
**Fix the JML annotations in the class `AnnotationSyntax` (above) so that there is no doubt about where the JML annotations are and what are Java comments or annotations.**

**Learning Objectives:** 
+ Understand the difference between JML annotations and Java comments

## **[Answer Key](SyntaxExKey)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**

## Resources
+ [Question 1 Java file](AnnotationSynatx.java) the `AnnotationSyntax` class above.
