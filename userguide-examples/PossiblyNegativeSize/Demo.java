public class Demo {

  static public int[] demo(int i) {
    return new int[i];
  }
  
  //@ requires i >= 0;
  static public int[] demo2(int i) {
    return new int[i];
  }
  

}
