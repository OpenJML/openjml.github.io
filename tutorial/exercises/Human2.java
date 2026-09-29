// openjml --esc Human2.java
public class Human2 extends Animal2 {
    //@ public model boolean discount; //@ in age;
    protected boolean _discount = false; //@ in discount;
    //@ protected represents discount = _discount;

    /*@ also
      @   requires age <= a && 65 <= a && a <= 150;
      @   assignable age;
      @   ensures discount;   @*/
    public void setAge(int a) {
        if (a < _age) { return; }
	super.setAge(a);
 	if (65 <= a) { _discount = true; }
    }

    //@ requires g.equals("female")||g.equals("male");
    //@ ensures gender.equals(g);
    public Human2(String g) {
        super(g);
    }
}
