public class WellDefinedExample1 {
	
	//@ requires a != null;
	//@ ensures (\exists int i; 0 <= i < a.length; a[i] == key) || \result == -1;
	public int search(int[] a, int key) {
		int i;
		for(i = 0; i < a.length; i++) {
			//@ assume 0 <= i < a.length;
			if(a[i] == key) { 
				//@ assert a[i] == key;
				return i;	
			}
		}
		//@ assert !(\exists int j; 0 <= j < a.length; a[j] == key);
 		return -1;
	}

}