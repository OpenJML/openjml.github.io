public class Demo {

  //@ inline final pure
  public void callee(int i) {
    //@ assert i > 0;
  }

  public void caller() {
    callee(10);
    callee(-10);
  }
}
