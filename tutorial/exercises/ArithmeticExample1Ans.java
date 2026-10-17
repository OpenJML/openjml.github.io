// openjml --esc ArithmeticExample1Ans.java
public class ArithmeticExample1Ans {
	
	private int sum;

	public void sumThreeNums(int n1, int n2, int n3) {
            //@ assume Integer.MIN_VALUE <= n1 + n2 <= Integer.MAX_VALUE;
            //@ assume Integer.MIN_VALUE <= n2 + n3 <= Integer.MAX_VALUE;
            //@ assume 0 <= n1 + n2 + n3 <= Integer.MAX_VALUE;
            sum = n1 + n2 + n3;
            //@ assert 0 <= sum <= Integer.MAX_VALUE;	
	}
	
}
