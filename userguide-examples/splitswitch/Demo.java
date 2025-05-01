public class Demo {

  public static void test(int i) {
    //@ split
    switch (i) {
      case 0:
        //@ assert i > 1;
        break;
      case 1:
        //@ assert i == 1;
        break;
      default:
        //@ assert i == 0;
    }
  }
}
