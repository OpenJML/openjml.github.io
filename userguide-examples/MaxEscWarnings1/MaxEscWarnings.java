public class MaxEscWarnings {

  //@ ensures \result == 100;
  public static int test(int i, int j) {
    if (i > j) {
      return j;
    } else if (i < j) {
      return 100;
    }
    return i;
  }
}

