// openjml --esc T_constructors2.java
public class T_constructors2 {

  public static int count = 0;

  //@ public normal_behavior
  //@  requires count < Integer.MAX_VALUE;
  //@  assigns count;
  //@  ensures count == \old(count) + 1;
  public T_constructors2() {
    count++;
  }
}
