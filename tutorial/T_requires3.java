// openjml --esc --nullable-by-default T_requires3.java
public class T_requires3 {

  //@ requires a != null;
  //@ requires 0 <= index < a.length;
  //@ ensures \result == a[index];
  public int getElement(int[] a, int index) {
    return a[index];
  }
}
