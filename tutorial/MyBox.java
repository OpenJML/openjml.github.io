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
  //@ pure helper
  public int sizeH() {
    return size;
  }

  //@ private normal_behavior
  //@   assigns size;
  //@ helper
  private void changeSizeH() {
  }

  public static void test1(MyBox b) {
    //@ assert b.size() >= 0;
  }
  public static void test2(MyBox b) {
    //@ assert b.sizeH() >= 0; // OK because sizeH() is pure
  }
  public static void test3(MyBox b) {
    b.changeSizeH();
    //@ assert b.sizeH() >= 0; // FAILS -- changeSizeH does not necessarily establish the invariant
    b.size = 0;
  }
  public static void test4(MyBox b) {
    b.changeSizeH();
    //@ assert b.size() >= 0; // FAILS -- invariants not necessarily true, so size() is not allowed to be called
    b.size = 0;
  }
}
