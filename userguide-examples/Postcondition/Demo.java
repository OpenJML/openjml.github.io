public class Demo {

  static public void demo(int i) {
    mm(i);
  }

  //@ requires i > 0;
  //@ ensures \result == 1;
  //@ also
  //@ requires i == 0;
  //@ ensures \result == 0;
  //@ also
  //@ requires i < 0;
  //@ ensures \result == -1;
  //@ pure
  static Integer mm(int i) { // NonNull by default
    if (i > 0) return 1;
    if (i < 0) return -1;
    return null;
  }
}
