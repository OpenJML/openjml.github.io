// openjml --esc JMLExprExample1.java
public class JMLExprExample1 {
    
//@ requires num > 0;
// write a postcondition for the method below
public boolean primeChecker(int num) {
	boolean flag = true;
        int i;
	for (i = 2; i < num/2; i++) {
                //@ assume flag && 2 <= i;
		if (num % i == 0) {
			flag = false;
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
