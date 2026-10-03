// openjml --esc AssertExample2.java
public class AssertExample2 {
    
public boolean primeChecker(int num) {
        //@ assume num > 0;
	boolean flag = true;
	for (int i = 2; i <= num / 2; i++) {
                //@ assume i > 0;
                // first assert here
		if (num % i == 0) {
			flag = false;
			// second assert here
			return flag;
		}
	}
	// third assert here
	return flag;
}

}
