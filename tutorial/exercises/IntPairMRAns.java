// openjml --esc IntPairMRAns.java
public class IntPairMRAns {

    //@ public model boolean mincreasing;
    //@ public model int mlesser, mgreater;
    //@ public model int first, second;
    
    private final int lesser; //@ in mlesser;
    private final int greater; //@ in mgreater;
    private final boolean increasing; //@ in mincreasing;

    //@ private represents mincreasing = increasing;
    //@ private represents mlesser = lesser;
    //@ private represents mgreater = greater;
    //@ private represents first = (increasing ? lesser : greater);
    //@ private represents second = (increasing ? greater : lesser);

    //@ public invariant mlesser <= mgreater;
    //@ public invariant mlesser <= first && mlesser <= second;
    //@ public invariant first <= mgreater && second <= mgreater;

    //@ ensures first == fv && second == sv;
    public IntPairMRAns(int fv, int sv) {
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
