// openjml --esc $@
public class T_PureMethod {

  //@ requires i > Integer.MIN_VALUE;
  //@ ensures \result >= 0;
  //@ pure
  public static int abs(int i) {
    return i >= 0 ? i : -i;
  }

  public void test(int k) {
    //@ assert k > 0 ==> abs(k) == k;
  }
}
