// openjml --esc AssertExample2.java
public class AssertExample2 {
    
public boolean primeChecker(int num) {
        //@ assume num > 0;
	boolean isPrime = true;
        int i;
	for (i = 2; i < num/2; i++) {
                //@ assume isPrime && 2 <= i;
		if (num % i == 0) {
			// first assert here
			isPrime = false;
			return isPrime;
		}
	}
        //@ assume isPrime && 2 <= i;
        if (num % i == 0) {
            isPrime = false;
            return isPrime;
        }
	// second assert here
	return isPrime;
}

}
