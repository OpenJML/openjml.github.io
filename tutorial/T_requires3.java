// openjml --esc --nullable-by-default T_requires3.java
public class T_requires3 {

  //@ requires 0 <= index < a.length;
  //@ requires a != null;  // out of order!
  //@ ensures \result == a[index];
  public int getElement(int[] a, int index) {
    return a[index];
  }
}
