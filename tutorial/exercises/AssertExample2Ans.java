// openjml --esc AssertExample2Ans.java
public class AssertExample2Ans {
    
public boolean primeChecker(int num) {
        //@ assume num > 0;
	boolean flag = true;
        int i;
	for (i = 2; i < num/2; i++) {
                //@ assume flag && 2 <= i;
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
