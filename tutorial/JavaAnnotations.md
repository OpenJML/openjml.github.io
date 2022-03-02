---
title: JML Tutorial - Java Annotations and JML Annotation comments
---

This tutorial describes how to use JML annotation comments --- `//@ pure` --- and the like to write specifications for Java programs.
The word 'annotation' is a bit ambiguous because (after the origin of JML) Java added to its  programming language a concept of annotation interfaces.
These also begin with the `@` symbol, but are written in Java code, not in comments. The introduction of Java annotations sparked lots of work in many areas to see how such annotations could be put to good use.

The JML community also investigated this. The result of that research is the following:

The various kinds of JML modifiers for field, method and class declarations may also be expressed as Java annotations. So instead of `//@ pure` one can write `@Pure`; instead of `//@ spec_public` one can write `@SpecPublic`, and so on.

For example,
```
import org.jmlspecs.annotation.*;

public class T {
  @Pure
  int yieldnumber() {
    return 42;
  }
}
```

If you do use these Java annotations then
* you need to either include `import org.jmlspecs.annotation.*;` (or all the specific imports you use: `import org.jmlspecs.annotation.Pure;` etc.) in your Java program, or fully qualify the annotations when used: `@org.jmlspecs.annotation.Pure`; and
* anyone who is using the source code (e.g., compiling it) will need to have a copy of the jmlruntime.jar, which contains the definitions of the Java annotations for JML.

The annotations themselves are not needed at runtime (i.e., for RAC) but other classes in jmlruntime.jar are.

Because of the above limitations and the fact that the Java source code is being modified, these Java annotations for JML are less popular than simply using the JML annotation comments.

To complete this story, Java annotations were explored for other aspects of JML as well: `@Requires` for preconditions, `@Ensures` for postconditions, and so on.
These were even less convenient, because Java annotations can hold only compile-time constants, such as fixed strings. Tools would need to extract the JML strings from the annotations to parse and use them. Though this is not so different than extracting JML text from comments, it offered no advantage and made for much messier syntax. Consequently, no tools (beyond the first exploratory implementation) implemented Java annotations for JML other than for modifiers as presented above.

_Last modified: 2022-03-01 23:54:56_