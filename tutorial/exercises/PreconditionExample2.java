// openjml -esc PreconditionExample2.java
public class PreconditionExample2 {
	
	//@ requires a != null;
	//@ requires 0 <= low < a.length;
	//@ requires 0 <= high < a.length;
	//@ requires (\forall int i; 0 < i && i < a.length; a[i-1] <= a[i]);
	public int binarySearch(int[] a, int low, int high, int key) {
		int mid;		
		
		while(low <= high) {
			//@ assume 0 <= (low+high) < a.length;
			mid = (low+high)/2;
			if(a[mid] == key)
				return mid;
			if(a[mid] > key)
				high = mid - 1;
			if(a[mid] < key)
				low = mid + 1;
		}
		return -1;
	}
	

}