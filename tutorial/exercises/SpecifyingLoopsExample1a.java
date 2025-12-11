public class SpecifyingLoopsExample1a {
	
    //@ ensures \result.length() == str1.length();
	//@ ensures (\forall int j; 
	//@			0 <= j <= str1.length()-1; 
	//@			\result.charAt(j) == str1.charAt(str1.length()-j-1));
    //@ pure
	public String reverseWord(String str1) {
        final int length = str1.length();
        char[] str2 = new char[length];
		
        //@ maintaining 0 <= i <= length;
        //@ maintaining (\forall int j; 
        //@				0 <= j < i; 
        //@ 			str2[j] == str1.charAt(length-1-j));
        //@ loop_assigns str2[*];
        //@ decreases (length-1)-i;		
        for(int i = 0; i < length; i++) {
            str2[i] = str1.charAt(length-1-i);
        }
        String res = new String(str2);
        return res;
    }
}
