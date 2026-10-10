// openjml --esc PostCondEx2Ans.java
public class PostCondEx2Ans {

    //@ ensures \result == num/2;
    public int divideByTwo(int num) {
        return num/2;
    }
}
