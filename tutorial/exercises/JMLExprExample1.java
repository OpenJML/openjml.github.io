// openjml --esc JMLExprExample1.java
public class JMLExprExample1 {
    
//@ requires num > 0;
public boolean primeChecker(int num) {
	boolean flag;
	for (int i = 2; i <= num / 2; i++) {
		//@ assume i > 0;
		if (num % i == 0) {
			flag = false;
			//@ assert num % i == 0;
			//@ assert flag == false;
			return flag;
		}
	}

	flag = true;
	//@ assert flag == true;
	return flag;
}

}
