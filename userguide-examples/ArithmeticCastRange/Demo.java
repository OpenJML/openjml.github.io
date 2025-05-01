public class Demo {

  //@ requires 0 <= i && i < 32768;
  static public void demo(int i) {
    short k = (short)i;
    byte b = (byte)i; 
  }
}
