public class SumMax {


  //@ requires a.length > 0;
  void m(int[] a) {
    int sum = 0;
    int max = a[0];

    //@ loop_invariant 0 <= i <= a.length;
    //@ loop_invariant sum <= \count * max;
    for (int i=0; i<a.length; i++) {
      //@ assume sum + a[i] <= Integer.MAX_VALUE; // Just assume we never overflow
      //@ assume sum + a[i] >= Integer.MIN_VALUE; // Just assume we never overflow
      //@ assume max * a.length <= Integer.MAX_VALUE; // Just assume we never overflow
      //@ assume max * a.length >= Integer.MIN_VALUE; // Just assume we never overflow
      sum += a[i];
      if (max < a[i]) max = a[i];
    }
  }

}
