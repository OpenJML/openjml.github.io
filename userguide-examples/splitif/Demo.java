public class Demo {

  public static void test(int i) {
    //@ split
    if (i > 0) {
      //@ assert i > 1; // ERROR
    } else if (i < 0) {
      //@ assert i < -1; // ERROR
    } else {
      //@ assert i == 0; // OK
    }
  }
}
