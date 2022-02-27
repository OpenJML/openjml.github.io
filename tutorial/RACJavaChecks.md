# RAC and Java Checks

OpenJML checks for some program states that Java also checks for. When doing runtime-assertion-checking, those checks can happen twice.
So OpenJML will omit the RAC check if it is immediately followed by an identical Java check.
For example, with default settings, the file

```
//  openjml --rac T_RacJavaCheck.java && openjml-java -cp . T_RacJavaCheck 
public class T_RacJavaCheck {
  public static void main(String... args) {
    int[] array = new int[-1];
  }
}
```

produces
```
Exception in thread "main" java.lang.NegativeArraySizeException: -1
	at T_RacJavaCheck.main(T_RacJavaCheck.java:4)
```

If you want to see both the RAC check and the Java check, compile using the `-racJavaChecks` option:
`openjml -rac -racJavaChecks T_RacJavaCheck.java && openjml-java -cp . T_RacJavaCheck`
produces
```
T_RacJavaCheck.java:4: verify: JML attempt to create an array with negative size
    int[] array = new int[-1];
                          ^
Exception in thread "main" java.lang.NegativeArraySizeException: -1
	at T_RacJavaCheck.main(T_RacJavaCheck.java:4)
```

In most cases of such Java checks (e.g. null dereference, index out of bounds), Java will terminate with an exception, as ther is no way
to proceed after such an error (unless the program itself catches and handles the exception).
