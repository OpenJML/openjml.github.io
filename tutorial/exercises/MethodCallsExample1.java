public class MethodCallsExample1 {
	
	//@ requires (\forall int j; 0 <= j < a.length; a[j]+b[j] <= Integer.MAX_VALUE);
	//@ ensures \result.length == a.length || \result.length == 0;
	//@ pure
	public int[] addArrays(int[] a, int[] b) {
		
		if(sameSize(a, b)) {
			//@ assert sameSize(a, b);
			int[] newArr = new int[a.length];
			for(int i = 0; i < a.length; i++) {
				//@ assume 0 <= i < a.length;
				//@ assume Integer.MIN_VALUE < a[i] + b[i] <= Integer.MAX_VALUE;
				newArr[i] = a[i] + b[i];
			}	
			return newArr;
		}
		return new int[0];
	}
	
	//@ ensures \result <==> (a.length == b.length);
	//@ pure
	public boolean sameSize(int[] a, int[] b) {
		return a.length == b.length;
	}

}