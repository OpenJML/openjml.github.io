public class SpecifyingExceptionsExample1 {

	//@ requires 0 <= index < arr.length;
	//@ ensures \result == arr[index];
	//@ signals (Exception e) false;
	public int elementAtIndex(int[] arr, int index) {
		return arr[index];
	}
}