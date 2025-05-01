public class Demo {

  //@ requires 0 <= i;
  public static void test(int i) {
    int k = 0;
    //@ maintaining 0 <= k <= i;
    //@ decreases i-k;
    //@ loop_assigns k;
    //@ split
    while (k < i) {
      k++;
      //@ assert 0 <= k <= i; // OK
      //@ assert k == 0; // ERROR
    }
    //@ assert k == i; // OK
    //@ assert k == 10; // ERROR
  }
}
