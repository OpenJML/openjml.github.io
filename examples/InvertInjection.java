public class InvertInjection {

  static public int N;
  static public int M;
  static public int[] a;
  static public int[] b;
	
  //@ requires a != b; // Note - this is needed !
  //@ requires 0 <= N <= a.length;
  //@ requires 0 <= M <= b.length;
  //@ requires \forall int i; 0 <= i < N; 0 <= a[i] < M;
  //@ requires \forall int i,j; 0 <= i < j < N; a[i] != a[j];
  //@ ensures \forall int i; 0 <= i < N; b[a[i]] == i;
  //@ ensures \forall int i; 0 <= i < M; ((\forall int j; 0 <= j < N; a[j] != i) <==> b[i] == -1);
  //@ ensures \forall int j; 0 <= j < M; b[j] != -1 ==> a[b[j]] == j;
  public void invert() {

    //@ loop_invariant 0 <= k <= M;
    //@ loop_invariant \forall int i; 0 <= i < k; b[i] == -1;
    //@ loop_decreases M - k;
    for (int k = 0; k < M; k++) b[k] = -1;
  
    //@ loop_invariant 0 <= k <= N;
    //@ loop_invariant \forall int i; 0 <= i < k; b[a[i]] == i;
    //@ loop_invariant \forall int i; 0 <= i < M; ((\forall int j; 0 <= j < k; a[j] != i) <==> b[i] == -1);
    //@ loop_invariant \forall int j; 0 <= j < M; b[j] != -1 ==> a[b[j]] == j;
    //@ loop_decreases N - k;
    for (int k = 0; k < N; k++) {
      b[a[k]] = k;
    }
  }
}
