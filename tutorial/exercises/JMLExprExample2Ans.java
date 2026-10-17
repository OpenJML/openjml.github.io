// openjml --esc JMLExprExample2Ans.java
public class JMLExprExample2Ans {

    public boolean modusPonens(boolean p, boolean q) {
        if (p) {
            //@ assert q <==> (p ==> q);
            return q;
        } else {
            //@ assert p ==> q;
            return true;
        }
    }

}
