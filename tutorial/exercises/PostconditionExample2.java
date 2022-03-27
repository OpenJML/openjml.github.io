public class PostconditionExample2 {
	
	//@ requires w > 0 & h > 0;
	//@ requires w < Integer.MAX_VALUE & h < Integer.MAX_VALUE;
	//@ requires w*h < Integer.MAX_VALUE;
	//@ ensures \result > 0;
	//@ ensures \result >= w;
	//@ ensures \result >= h;
	public int area(int w, int h) {
		int A = w*h;
		return A;		
	}	
}
