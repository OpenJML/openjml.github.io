// This example was written by Viktorio S. el Hakim - 1/2021
// It establishes that the array is sorted, but not that it is a permutation of the input array

public class HeapSort {	
	
  /*@ requires 1 <= i <= len/2 && len <= arr.length;
      requires \forall int k;i < k <= len/2;arr[k-1] <= arr[2*k-1]; 
      requires \forall int k;i < k <= (len-1)/2;arr[k-1] <= arr[2*k];
      ensures \forall int k;i <= k <= len/2;arr[k-1] <= arr[2*k-1];
      ensures \forall int k;i <= k <= (len-1)/2;arr[k-1] <= arr[2*k]; 
  @*/
  public static void heapify(int /*@ non_null @*/ [] arr, final int i, final int len) {
    int j = i;
    /*@ loop_invariant i <= j <= len;
        loop_invariant \forall int k; j < k <= len/2; arr[k-1] <= arr[2*k-1];
        loop_invariant \forall int k; j < k <= (len-1)/2; arr[k-1] <= arr[2*k];
        loop_invariant \forall int k; i <= k < j && k <= len/2; arr[k-1] <= arr[2*k-1];
        loop_invariant \forall int k; i <= k < j && k <= (len-1)/2; arr[k-1] <= arr[2*k];
        loop_invariant \forall int k; 2*j-1 <= k-1 <= 2*j && k <= len && j > i;
                                      arr[k-1] >= arr[j/2-1]; 
        decreasing len-j;
      @*/
    while (true) {			
      int m = j;
      if (m <= len/2) {
        int c = 2*m;
        if (arr[c-1] < arr[m-1]) m=c;
        if (c < len && arr[c] < arr[m-1]) m=c+1;
      }
			
      if (m==j) break;
      int tmp = arr[j-1];
      arr[j-1] = arr[m-1];
      arr[m-1] = tmp;
      j = m;
    }
  }
	
  /*@
    requires 1 <= len <= arr.length;
    requires \forall int k; 1 <= k <= len/2; arr[k-1] <= arr[2*k-1];
    requires \forall int k; 1 <= k <= (len-1)/2; arr[k-1] <= arr[2*k]; 
    ensures  \result && \forall int k; 0 < k < len; arr[k] >= arr[0]; //Always true
  public static pure model boolean isGeq(final int  non_null [] arr, final int len) {
    loop_invariant 0 <= i < len;
    loop_invariant \forall int k;i < k < len;arr[k] >= arr[0];
    decreasing i;
    for (int i = len-1; i > 0; i--) {
      int j=i+1;
	
      loop_invariant 1 <= j <= i+1;
      loop_invariant arr[i] >= arr[j-1];
      decreasing j;
      while(j > 1) {
        j = j / 2;
      }
    }
    return \forall int k; 0 < k < len; arr[k] >= arr[0];
  }
  @*/
	
  /*@
    ensures \forall int k,j; 0 <= k < j < arr.length; arr[k] >= arr[j];
  @*/
  public static void sort(int /*@ non_null @*/ [] arr) {
    // Array of size 1 is already sorted
     if (arr.length < 2) return;
		
    // Build heap
    /*@ loop_invariant 0 <= i <= arr.length/2;
        loop_invariant \forall int k; i < k <= arr.length/2; arr[k-1] <= arr[2*k-1];
        loop_invariant \forall int k; i < k <= (arr.length-1)/2; arr[k-1] <= arr[2*k]; 
        decreasing i;
    @*/
    for (int i = arr.length/2; i > 0; i--) {
      heapify(arr,i,arr.length);
    }
		
    // Now sort
    int tmp;
    /*@ loop_invariant 1 <= len < arr.length;
        loop_invariant \forall int k;1 <= k <= (len+1)/2; arr[k-1] <= arr[2*k-1];
        loop_invariant \forall int k;1 <= k <= len/2; arr[k-1] <= arr[2*k]; 
        loop_invariant isGeq(arr,len+1);
        loop_invariant \forall int k,j; 0 <= k <= len < j < arr.length; arr[j] <= arr[k];
        loop_invariant \forall int k,j; len <= k < j < arr.length; arr[j] <= arr[k];
        decreasing len-1;
    @*/
    for (int len = arr.length-1; len>1; len--) {
      tmp = arr[0];
      arr[0] = arr[len];
      arr[len] = tmp;
      heapify(arr,1,len);
    }
    tmp = arr[0];
    arr[0] = arr[1];
    arr[1] = tmp;
  }
}
