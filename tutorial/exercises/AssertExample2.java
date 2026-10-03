// openjml --esc AssertExample2.java
public class AssertExample2 {
    
public boolean primeChecker(int num) {
        //@ assume num > 0;
	boolean flag = true;
        int i;
	for (i = 2; i < num/2; i++) {
                //@ assume flag && 2 <= i;
		if (num % i == 0) {
			// first assert here
			flag = false;
			return flag;
		}
	}
        //@ assume flag && 2 <= i;
        if (num % i == 0) {
            flag = false;
            return flag;
        }
	// second assert here
	return flag;
}

}
