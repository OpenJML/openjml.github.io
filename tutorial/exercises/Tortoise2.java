// openjml --esc Tortoise2.java
public class Tortoise2 extends Animal2 {
    protected int _age; //@ in age;
    //@ protected represents age = _age;

    //@ requires g.equals("female")||g.equals("male");
    //@ ensures gender.equals(g);
    //@ ensures age == 0;
    public Tortoise2(String g) {
        super(g);
        _age = 0;
        //@ assert age == 0;
    }
    
    /*@ also
      @   requires age <= a && 151<=a && a<=400;    
      @   assignable age;
      @   ensures age == a;          @*/
    public void setAge(int a)
    {
        if (a < _age) { return; }
        _age = a;
    }

    public static void test() {
        Tortoise2 t2 = new Tortoise2("female");
        t2.setAge(20);
        t2.setAge(10);
    }
}
