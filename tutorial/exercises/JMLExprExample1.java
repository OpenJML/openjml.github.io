// openjml --esc JMLExprExample1.java
public class JMLExprExample1 {
    
//@ requires num > 0;
// write a postcondition for the method below
public boolean primeChecker(int num) {
	boolean isPrime = true;
        int i;
	for (i = 2; i < num/2; i++) {
                //@ assume isPrime && 2 <= i;
		if (num % i == 0) {
			//@ assert num % i == 0;
			isPrime = false;
			return isPrime;
		}
                //@ assert isPrime;
	}
        //@ assume isPrime && 2 <= i;
        if (num % i == 0) {
            isPrime = false;
            return isPrime;
        }
        //@ assert isPrime;
	return isPrime;
}

}
