public class Demo {

  public static void test(int i) {
    //@ split i == 1;
    //@ assert i > 0; // OK for one split, not for the other
  }
}
