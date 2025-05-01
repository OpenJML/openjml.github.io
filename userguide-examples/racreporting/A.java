public class A {

  //@ requires i > 0;
  public static void m(int i) {
  }
  public static void main(String ... args) {
    m(0); // Precondition error
  }

}
