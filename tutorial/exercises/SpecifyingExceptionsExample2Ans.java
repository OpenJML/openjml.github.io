// openjml --esc SpecifyingExceptionsExample2Ans.java
public class SpecifyingExceptionsExample2Ans {

    //@ signals_only IllegalArgumentException;
    //@ signals (IllegalArgumentException) tableSize == 0;
    public int getHash(String str, int tableSize) {
        if(tableSize == 0) {
            throw new IllegalArgumentException();
        }
	return str.length() % tableSize;
    }
}
