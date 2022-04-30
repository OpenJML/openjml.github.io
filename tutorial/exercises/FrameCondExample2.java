public class FrameCondExample2 {
	//@ spec_public
	private int[] arr = new int[10];
	
	//@ requires arr != null;
	//@ requires 0 < increase < Integer.MAX_VALUE;
	//@ assigns arr;
	//@ ensures arr.length == \old(arr.length + increase); 
	public void increase(int increase) {
		//@ assume 0 <= (arr.length+increase) < Integer.MAX_VALUE;
		int[] newArr = new int[arr.length + increase];

		for (int i = 0; i < arr.length; i++) {
			//@ assume 0 <= i < arr.length;
			newArr[i] = arr[i];
		}

		arr = newArr;
	}
}