public class Demo {

  public static int[] arr;

  //@ requires 0 <= i;
  static public int demo(int i) {
    return arr[i];
  }
  
  //@ requires 0 <= i && i < arr.length ;
  static public int demo2(int i) {
    return arr[i];
  }

}
