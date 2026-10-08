// openjml --esc MyBox.java
public class MyBox {
  //@ spec_public 
  private int size;

  //@ public invariant size >= 0;

  //@ requires sz >= 0;
  public MyBox(int sz) {
    size = sz;
  }

  public void doit() {
    int[] ints = new int[size];
  }

  //@ assigns size;
  public void shrink() {   // ERROR: doesn't establish invariant on exit!
    size = size - 10;
  }

  //@ public normal_behavior
  //@   ensures \result == size;
  //@ spec_pure
  public int size() {
    return size;
  }

  //@ public normal_behavior
  //@   ensures \result == size;
  //@ spec_pure
  //@ helper    // does not assume the invariant
  public int sizeH() {
    return size;
  }

  //@ public normal_behavior
  //@   assigns size;
  //@ helper // does not assume or establish the invariant
  final public void changeSizeH() {
      java.util.Random r = new java.util.Random();
      int sz = r.nextInt(-10,10);
      size = sz;
  }

  public static void test1(MyBox b) {
    //@ assert b.size() >= 0;
  }
  public static void test2(MyBox b) {
    //@ assert b.sizeH() >= 0; // OK because sizeH() is pure
  }
  public static void test3(MyBox b) {
    //@ check b.size >= 0;
    b.changeSizeH();
    //@ check b.sizeH() == b.size;
    //@ check b.sizeH() >= 0; // ERROR: sizeH may not establish the invariant!
    b.size = 0;
  }
  public static void test4(MyBox b) {
    b.changeSizeH();
    //@ assert b.size() >= 0; // ERROR: invariants may not hold, so size() can't be called!
    b.size = 0;
  }
}
