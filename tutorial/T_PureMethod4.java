// openjml --esc T_PureMethod4.java 
public class T_PureMethod4 {

  //@ requires i > Integer.MIN_VALUE;
  //@ ensures \result >= 0;
  //@ spec_pure
  public static int abs(int i) {
    return i >= 0 ? i : -i;
  }

  public void test(int k) {
    //@ assert k >= 0 ==> abs(k) >= k;
  }
}
