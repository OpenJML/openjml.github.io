// openjml --esc MultMethodBehaviorEx1Ans.java
public class MultMethodBehaviorEx1Ans {

    //@   public normal_behavior
    //@     requires 0 < totalNum;
    //@     ensures \result == sum/totalNum;
    //@ also
    //@   public exceptional_behavior
    //@     requires totalNum == 0;
    //@     signals_only ArithmeticException;
    public int mean(int sum, int totalNum) {
        if(totalNum == 0) {
            throw new ArithmeticException();
        }
        return sum/totalNum;
    }
}
