// openjml --esc JMLExprExample2Ans1.java
public class JMLExprExample2Ans1 {

    public boolean modusPonens(boolean p, boolean q) {
        //@ assert (!p || q) <==> (p ==> q);
        return !p || q;
    }

}
