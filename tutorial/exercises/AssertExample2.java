public class AssertExample2 {

	//@ requires num > 0;
	//@ ensures \result <==> !(\exist int i; i >= 2; num % i == 0);
	public boolean primeChecker(int num) {
		boolean isPrime;
		for (int i = 2; i <= num / 2; i++) {
			//@ assume i > 0;
			if (num % i == 0) {
				//first assertion here
				//@ assert num % i == 0;
				isPrime = false;
				//second assertion here 
				//@ assert isPrime == false;
				return isPrime;
			}
		}
		
		isPrime = true;
		//third assertion here
		//@ assert isPrime == true;
		return isPrime;
	}
}