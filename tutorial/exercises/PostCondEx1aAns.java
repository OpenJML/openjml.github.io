// openjml --esc PostCondEx1aAns.java
public class PostCondEx1aAns {

    //@ requires -1 < num < 100;
    //@ ensures num <= \result;
    public int multiplyByTwo(int num) {
	return num*2;
    }
}
