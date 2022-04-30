public class FrameCondExample1 {
	
	//@ requires sameSize(a, b);
	//@ requires (\forall int j; 0 <= j < a.length; a[j]+b[j] <= Integer.MAX_VALUE);
	//@ assigns a[*];
	//@ ensures a.length == \old(a.length);
	public void addArrays(int[] a, int[] b) {
			
		if(sameSize(a, b)) {
			//@ assert sameSize(a, b);
			int[] temp = a;
			for(int i = 0; i < a.length; i++) {
				//@ assume 0 <= i < a.length;
				//@ assume Integer.MIN_VALUE < a[i] + b[i] <= Integer.MAX_VALUE;
				a[i] = temp[i] + b[i];
			}	
		}
	}
		
	//@ ensures \result <==> (a.length == b.length);
	//@ assigns \nothing;
	//@ pure
	public boolean sameSize(int[] a, int[] b) {
		return a.length == b.length;
	}
}