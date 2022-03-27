public class PostconditionExample1 {

	//@ requires num > 0;
	//@ requires num < Integer.MAX_VALUE;
	//@ requires num*2 < Integer.MAX_VALUE;
	//@ ensures \result > num;
	public int multiplyByTwo(int num) {
		return num*2;
	}
}
