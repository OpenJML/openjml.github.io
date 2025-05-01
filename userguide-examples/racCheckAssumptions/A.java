public class A {

  public static void main(String ... args) {
    m(args.length);
    mm(args.length);
  }

  //@ requires i == 1;
  //@ ensures \result == 20;
  public static int m(int i) {
    return 10;
  }

  //@ requires i == 0;
  //@ ensures \result == 20;
  public static int mm(int i) {
    return 10;
  }
}
