// openjml --esc PostCondEx1b.java
public class PostCondEx1b {

//@ requires -1 < num < 100;
//@ ensures num <= \result;
 public int multiplyByTwo(int num) {
	return num*2;
}

}
