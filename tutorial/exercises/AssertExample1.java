public class AssertExample1 {
	
	// @ ensures \result >= a && \result >= b && \result >= c;
	// @ ensures \result == a || \result == b || \result == c;
	public void max(int a, int b, int c) {
		int max;
		if(a >= b && a >= c) {
			max = a;
		}else if(b >= a && b >= c) {
			max = b;
		}else {
			max = c;
		}		
		
		//@ assert max >= a && max >= b && max >= c;
		//@ assert max == a || max == b || max == c;
	}

}