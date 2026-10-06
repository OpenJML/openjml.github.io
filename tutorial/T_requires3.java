// openjml --esc T_requires3.java
/*@ nullable_by_default @*/ public class T_requires3 {

  //@ requires 0 <= index;
  //@ requires index < a.length;   // ERROR: a may be null!
  //@ requires a != null;   // out of order!
  //@ ensures \result == a[index];
  public int getElement(int[] a, int index) {
    return a[index];
  }
}
