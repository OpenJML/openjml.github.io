public class SpecifyingExceptionsExample2 {
	
	/*@ requires str == null;
    @   signals_only NullPointerException;
    @ also
    @   requires str != null && tableSize == 0;
    @   signals_only ArithmeticException;
    @ also
    @   requires str != null && tableSize > 0;
    @   ensures \result == str.length % tableSize; 
    @*/
	public int getHash(String str, int tableSize) {
		if(str == null) throw new NullPointerException();
		if(tableSize == 0) throw new ArithmeticException();
		
		return str.length()%tableSize;
	
	}
	
}
