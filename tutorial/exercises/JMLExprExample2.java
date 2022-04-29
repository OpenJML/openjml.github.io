public class JMLExprExample2 {

	//@ ensures \result <==> (p==>q);	
	public boolean modusPonens(boolean p, boolean q) {
		if (p == true) {
			if (q == true) {
				return true;
			} else {
				return false;
			}
		} else {
			return true;
		}
	}

}
