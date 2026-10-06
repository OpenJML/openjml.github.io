// openjml --esc T_requires2.java
public class T_requires2 {

  //@ requires 0 <= index;
  //@ requires index < a.length;
  public int getElement(int[] a, int index) {
    return a[index];
  }
}
