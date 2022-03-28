public class AssertExample2 {

	//@ requires num > 0;
	//@ ensures \result <==> !(\exist int i; i >= 2; num % i == 0);
	public boolean primeChecker(int num) {
		boolean flag;
		for (int i = 2; i <= num / 2; i++) {
			//@ assume i > 0;
			if (num % i == 0) {
				flag = false;
				//first assertion here
				//@ assert num % i == 0;
				//second assertion here 
				//@ assert flag == false;
				return flag;
			}
		}
		
		flag = true;
		//third assertion here
		//@ assert flag == true;
		return flag;
	}
}