// openjml --esc SpecifyingExceptionsExample2.java
public class SpecifyingExceptionsExample2 {

    //@ signals_only \nothing;
    public int getHash(String str, int tableSize) {
        if(tableSize == 0) {
            throw new IllegalArgumentException();   // ERROR: throws exception!
        }
	return str.length() % tableSize;
    }
}
