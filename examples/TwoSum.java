public class TwoSum {

  class Pair {
    int i;
    int j;
    //@ ensures i == ii && j == jj;
    Pair(int ii, int jj) {
      i = ii;
      j = jj;
    }
  }

  // Naive solution: quadratic search
  //@ ensures \result != null <==> \exists int i, j; 0 <= i < a.length && 0 <= j < a.length; a[i] + a[j] == sum;
  //@ ensures \result != null ==> a[\result.i] + a[\result.j] == sum;
  //@ nullable  code_java_math spec_java_math // Ignore addition overflow
  Pair twoLoop(int[] a, int sum) {
    //@ loop_invariant 0 <= i <= a.length;
    //@ loop_invariant !\exists int ii, j; 0 <= ii < i && 0 <= j < a.length; a[ii] + a[j] == sum;
    for (int i=0; i < a.length; i++) {
      //@ loop_invariant 0 <= j <= a.length;
      //@ loop_invariant !\exists int jj; 0 <= jj < j; a[i] + a[jj] == sum;
      for (int j = 0; j < a.length; j++) {
        if (a[i] + a[j] == sum) return new Pair(i,j);
      }
    }
    return null;
  }

  // Linear solution in which all entries are non-negative, so an array can be used to record seen entries
  //@ requires  0 <= sum < Integer.MAX_VALUE;
  //@ requires \forall int i; 0 <= i < a.length; 0 <= a[i] < Integer.MAX_VALUE/2;
  //@ ensures \result != null <==> \exists int i, j; 0 <= i < a.length && 0 <= j < a.length; a[i] + a[j] == sum;
  //@ ensures \result != null ==> a[\result.i] + a[\result.j] == sum;
  //@ nullable
  Pair oneLoopPositive(int[] a, int sum) {
    int[] seen = new int[sum+1];
    //@ loop_invariant \forall int k; 0 <= k < seen.length; 0 <= seen[k] <= a.length;
    //@ loop_invariant 0 <= i <= a.length;
    //@ loop_invariant !\exists int ii, j; 0 <= ii < i && 0 <= j < i; a[ii] + a[j] == sum;
    //@ loop_invariant \forall int k; 0 <= k < seen.length; seen[k] == 0 <==> !\exists int j; 0 <= j < i; a[j] == k;
    //@ loop_invariant \forall int k; 0 <= k < seen.length; seen[k] != 0 ==> a[seen[k]-1] == k;
    for (int i = 0; i < a.length; i++) {
      if (a[i] <= sum) {
        seen[a[i]] = i+1;
        int j = seen[sum-a[i]];
        if (j != 0) return  new Pair(i, j-1);
      }
    }
    return null;
  }
}
