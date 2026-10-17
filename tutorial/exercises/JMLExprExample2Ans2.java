// openjml --esc JMLExprExample2Ans2.java
public class JMLExprExample2Ans2 {

    public boolean modusPonens(boolean p, boolean q) {
        //@ assert (p ? q : true) <==> (p ==> q);
        return p ? q : true;
    }

}
