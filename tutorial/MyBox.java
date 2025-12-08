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
  public void shrink() {
    size = size - 10; // FAILS to establish invariant on exit
  }

  //@ public normal_behavior
  //@   ensures \result == size;
  //@ pure
  public int size() {
    return size;
  }

  //@ public normal_behavior
  //@   ensures \result == size;
  //@ pure helper // does not assume the invariant
  public int sizeH() {
    return size;
  }

  //@ public normal_behavior
  //@   assigns size;
  //@ helper // does not assume or establish the invariant; may set size to anything
  final public void changeSizeH() {
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
    //@ check b.sizeH() >= 0; // FAILS -- changeSizeH does not assume nor is required to establish the invariant
                               //          so the assertion may fail
    b.size = 0;
  }
  public static void test4(MyBox b) {
    b.changeSizeH();
    //@ assert b.size() >= 0; // FAILS -- invariants not necessarily true, so size() is not allowed to be called
    b.size = 0;
  }
}
