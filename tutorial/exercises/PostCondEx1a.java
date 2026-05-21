// openjml --esc PostCondEx1a.java
public class PostCondEx1a {

//@ requires 0 < num;
//@ ensures \result > num;
 public int multiplyByTwo(int num) {
	return num*2;
}

}
