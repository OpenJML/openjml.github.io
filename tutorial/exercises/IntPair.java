// openjml --esc IntPair.java
public class IntPair {

    private /*@ spec_public @*/ final int lesser, greater;
    private /*@ spec_public @*/ final boolean increasing;

    //@ public ghost final int first;
    //@ public ghost final int second;

    //@ public invariant lesser <= greater;
    //@ public invariant lesser <= first && lesser <= second;
    // the following is a "representation invariant"
    //@ public invariant increasing ==> (first == lesser && second == greater);
    //@ public invariant !increasing ==> (second == lesser && first == greater);

    //@ ensures first == fv && second == sv;
    public IntPair(int fv, int sv) {
        //@ set first = fv;
        //@ set second = sv;
        increasing = (fv <= sv);
        if (increasing) {
            lesser = fv;
            greater = sv;
        } else {
            lesser = sv;
            greater = fv;
        }
   }

    //@ ensures \result <= first && \result <= second;
    //@ spec_pure
    public int lesserValue() {
        return lesser;
    }

    //@ ensures \result == first;
    //@ spec_pure
    public int firstElem() {
        return (increasing ? lesser : greater);
    }
}
