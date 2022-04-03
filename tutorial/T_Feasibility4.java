// openjml --esc --check-feasibility=call T_Feasibility4.java
abstract class A {
    public int kk;
    //@ ensures kk == \old(kk) + 1;
    //@ pure // faulty spec
    abstract public void mm();
}
abstract public class T_Feasibility4 extends A {
    //@ requires i > 0;
    public void m(int i) {
	mm();
    }
}

