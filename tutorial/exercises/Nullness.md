---
title: JML Tutorial - Exercises - Nullable and non-null values and types
---
# Exercises:
## [Nullness Tutorial](https://www.openjml.org/tutorial/Nullness)

## **Question 1**
**Consider the following code, which does _not_ verify in JML.**
```Java
public class ObjPair {
    private /*@ spec_public @*/ Object fst, snd;

    //@ requires f != s;
    //@ ensures fst == f && snd == s && fst != snd;
    public ObjPair(Object f, Object s) {
        fst = f;
        snd = s;
    }

    public static void test() {
        Integer five = Integer.valueOf(5);
        Integer seven = Integer.valueOf(7);
        ObjPair p = new ObjPair(five, seven);
        //@ assert p.fst != p.snd;
        ObjPair op = new ObjPair(null, seven); // <-- this line wrong!
    }
}
```

(a) **Why does the line marked as wrong in the method `test()` not verify?**

(b) **What could be done to the method `test()` to make the code verify?**

(c) **Aside from changing the method `test()`, what else could be done
    so that the program would verify?**

## **[Answer Key](NullnessExKey.md)**

## **Resources:**
+ [Question 1 Java](ObjPair.java)
+ [Question 2 Java](.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
