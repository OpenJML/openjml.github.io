// openjml --check JMLExprExample1Ans.java
public class JMLExprExample1Ans {
    
//@ requires num > 0;
//@ ensures \result <==> !(\exists int i; i >= 2; num % i == 0);
public boolean primeChecker(int num) {
	boolean flag;
	for (int i = 2; i <= num / 2; i++) {
		//@ assume i > 0;
		if (num % i == 0) {
			//@ assert num % i == 0;
			flag = false;
			return flag;
		}
                //@ assert flag;
	}
        //@ assume flag && 2 <= i;
        if (num % i == 0) {
            flag = false;
            return flag;
        }
        //@ assert flag;
	return flag;
}

}
