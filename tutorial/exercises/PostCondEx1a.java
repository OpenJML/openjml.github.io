// openjml --esc PostCondEx1a.java
public class PostCondEx1a {

 //@ requires -1 < num < 100;
 //@ ensures num < \result;
 public int multiplyByTwo(int num) {
     return num*2;
 }

}
