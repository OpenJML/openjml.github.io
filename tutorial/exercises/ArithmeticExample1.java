// openjml --esc ArithmeticExample1.java
public class ArithmeticExample1 {
	
    private int sum;

    public void sumThreeNums(int n1, int n2, int n3) {
        sum = n1 + n2 + n3;   // ERROR: may overflow!
	//@ assert 0 <= sum <= Integer.MAX_VALUE;   // ERROR: may fail!
    }
	
}
