public class Demo {

  static public int field;

  //@ ensures  field == i;
  //@ signals (Exception e) field == i;
  static public void demo(int i) {
    init();
    field = i;
  }

  /*@ pure */ static void init() {
  }
}

