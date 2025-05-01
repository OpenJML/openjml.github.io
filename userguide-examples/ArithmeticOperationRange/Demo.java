public class Demo {

  static public void demo(int i) {
    int kkk = i + i + i;
    int k = i * i;
  }

  //@ requires i >= 0 && i < 32000;
  static public void demo2(int i) {
    int kk = i + i;
    int k = i * i * i * i;
  }
}
