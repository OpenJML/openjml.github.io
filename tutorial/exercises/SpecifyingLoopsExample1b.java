public class SpecifyingLoopsExample1 {
	//@ ensures \result.length() == str1.length();
    	//@ ensures (\forall int j; 
	//@			0 <= j <= str1.length()-1; 
	//@			\result.charAt(j) == str1.charAt(str1.length()-j-1));
	//@ pure
    public String reverseWord(String str1) {
        final int length = str1.length();
        char str2[] = new char[length];
		
        //@ maintaining -1 <= i <= length-1;
        //@ maintaining (\forall int j; 
        //@				0 <= j < (length-1)-i; 
        //@				str2[j] == str1.charAt(length-1-j));
        //@ loop_assigns str2[*];
        //@ decreases i+1;		
        for(int i = length-1; 0 <= i; i--) {
            str2[(length-1)-i] = str1.charAt(i);
        }
        String res = new String(str2);
        return res;
    }
}
