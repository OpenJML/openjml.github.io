public class Demo {

  static public void demo(int i) {
    mm(i);
  }

  //@ requires i > 0;
  //@ ensures \result == 1;
  //@ also
  //@ requires i < 0;
  //@ ensures \result == -1;
  //@ pure
  static int mm(int i) {
    if (i > 0) return 1;
    if (i < 0) return -1;
    return i;
  }
}
