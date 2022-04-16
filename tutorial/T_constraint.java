// openjml --esc T_constaint.java
//@ code_java_math spec_java_math
public class T_constraint {

  public int count;
  //@ public initially count == 0;
  //@ public constraint count == \old(count) + 1;

  public T_constraint() {
    count = 0;
  }

  public void m1() {
    count++;
  }

  public void m2() {
  }

  public static void m3() {
  }
}
