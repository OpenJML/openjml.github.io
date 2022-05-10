public class ArithmeticExample1 {
	
	//@ spec_public
	private int sum;

	//@ requires 0 < n1 < Integer.MAX_VALUE;
	//@ requires 0 < n2 < Integer.MAX_VALUE;
	//@ requires 0 < n3 < Integer.MAX_VALUE;
	//@ requires n2 < Integer.MAX_VALUE/n3;
	//@ requires n1 < Integer.MAX_VALUE/(n2 + n3);
	//@ assigns sum;
	//@ ensures 0 < sum < Integer.MAX_VALUE;
	public void sumThreeNums(int n1, int n2, int n3) {
		sum = n1 + n2 + n3;
	}
	
}