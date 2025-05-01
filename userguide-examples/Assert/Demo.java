public class Demo {

  static public int demo(int i) {
    if (i > 0) return 1;
    //@ assert i < 0;
    return i;
  }

  //@ requires i >= 0;
  static public int demo2(int i) {
    if (i > 0) return 1;
    //@ assert i == 0;
    return i;
  }
}
