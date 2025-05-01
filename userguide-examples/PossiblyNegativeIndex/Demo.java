public class Demo {

  public static int[] arr;

  //@ requires i < arr.length;
  static public int demo(int i) {
    return arr[i];
  }
}
