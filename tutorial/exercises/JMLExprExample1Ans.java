// openjml --check JMLExprExample1Ans.java
public class JMLExprExample1Ans {
    
//@ requires num > 0;
//@ ensures \result <==> !(\exists int i; 2 <= i && i < num/2; num % i == 0);
public boolean primeChecker(int num) {
	boolean isPrime = true;
        int i;
	for (i = 2; i < num/2; i++) {
                //@ assume isPrime && 2 <= i && i < num/2;
                //@ assume !(\exists int j; 2 <= j && j < i; num % j == 0);
		if (num % i == 0) {
			//@ assert num % i == 0;
			isPrime = false;
			return isPrime;
		}
                //@ assert isPrime && 2 <= i && i < num/2;
                //@ assert !(\exists int j; 2 <= j && j < i; num % j == 0);
	}
        //@ assume isPrime && 2 <= i && i == num/2;
        //@ assert !(\exists int j; 2 <= j && j < i; num % j == 0);
        if (num % i == 0) {
            isPrime = false;
            return isPrime;
        }
        //@ assert !(\exists int j; 2 <= j && j <= num/2; num % j == 0);
        //@ assert isPrime;
	return isPrime;
}

}
