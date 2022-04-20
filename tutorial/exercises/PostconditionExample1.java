public class PostconditionExample1 {

	//@ requires num > 0;
	//@ requires num < Integer.MAX_VALUE;
	//@ requires num < Integer.MAX_VALUE/2;
	//@ ensures \result > num;
	public int multiplyByTwo(int num) {
		return num*2;
	}
}
