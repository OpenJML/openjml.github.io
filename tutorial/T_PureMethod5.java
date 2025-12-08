// openjml --esc T_PureMethod5.java 
public class T_PureMethod5 {
  //@ spec_public
  int[] a = new int[10];

  //@ requires 0 <= i & i < a.length;
  //@ ensures \result == a[i];
  //@ spec_pure
  public int elementAt(int i) {
    return a[i];
  }

  public void test1() {
    //@ assert elementAt(0) == 0;
  }

  public void test2() {
    //@ assert elementAt(-1) == 0;
  }
}
