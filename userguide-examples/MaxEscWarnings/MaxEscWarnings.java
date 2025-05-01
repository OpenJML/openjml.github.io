public class MaxEscWarnings {

  public static void test(int i, int j) {
    if (i > j) {
      //@ assert j == 0;;
    } else {
      //@ assert i == 0;
    }
  }
}

