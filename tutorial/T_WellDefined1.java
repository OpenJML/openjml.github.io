// openjml --esc T_WellDefined1.java
public class T_WellDefined1 {

  public void example(int[] a, int i) {
    //@ assert a[i] == 0;    // ERROR: i might be an illegal index!
  }
}
