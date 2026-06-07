public class MethodCallsEx1 {

    /*@ requires (\forall int j; 0 <= j < a.length; 0 <= a[j] && 0 <= b[j]
      @                            && 0 <= a[j]+b[j] <= Integer.MAX_VALUE); @*/
    //@ ensures (a.length == b.length && \result.length == a.length) || \result.length == 0;
    //@ ensures ((a.length == b.length) ==> (\forall int j; 0 <= j < a.length; \result[j] == a[j] + b[j]));
    //@ pure
    public int[] addArrays(int[] a, int[] b) {
	if(sameSize(a, b)) {
		int[] newArr = new int[a.length];
                int i = 0;
                //@ maintaining 0 <= i <= a.length;
                /*@ maintaining (\forall int j; 0 <= j < i;
                  @                     newArr[j] == a[j] + b[j]); @*/
		for(; i < a.length; i++) {
        		newArr[i] = a[i] + b[i];
		}
		return newArr;
	}
	return new int[0];
    }

    //@ ensures \result <==> (a.length == b.length);
    //@ spec_pure
    public boolean sameSize(int[] a, int[] b) {
	return a.length == b.length;
    }
}
