package exercises;

public class AssumeExample1 {
	
	//@ requires a != null;
	//@ ensures \result.length == a.length;
	public int[] reverseArray(int[] a) {
		int len = a.length;
		int[] b = new int[len];

		for (int i = 0; i < a.length; i++) {
			//@ assume 0 <= i < a.length;
			//@ assume 0 <= len-1 < a.length;
			b[len - 1] = a[i];
			len--;			
		}
		//@ assert b.length == a.length;
		return b;

	}

}