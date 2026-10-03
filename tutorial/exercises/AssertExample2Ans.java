// openjml --esc AssertExample2Ans.java
public class AssertExample2Ans {
    
public boolean primeChecker(int num) {
        //@ assume num > 0;
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
