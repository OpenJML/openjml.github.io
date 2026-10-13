// openjml --esc JMLExprExample1.java
public class JMLExprExample1 {

public boolean primeChecker(int num) {
        //@ assume 0 < num;
	boolean isPrime = true;
        int i;
	for (i = 2; i < num/2; i++) {
                //@ assume isPrime && 2 <= i < num/2;
                //@ assume !(\exists int j; 2 <= j < i; num % j == 0);
		if (num % i == 0) {
			//@ assert num % i == 0;
			isPrime = false;
			return isPrime;
		}
                //@ assert isPrime && 2 <= i < num/2;
                //@ assert !(\exists int j; 2 <= j < i; num % j == 0);
	}
        //@ assume isPrime && 2 <= i && i == num/2;
        //@ assume !(\exists int j; 2 <= j < i; num % j == 0);
        if (num % i == 0) {
            isPrime = false;
            return isPrime;
        }
        //@ assert isPrime;
        // write an assert statement here about num
	return isPrime;
}

}
