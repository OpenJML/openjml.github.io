public class Tortoise extends Animal2 {
    protected int _age; //@ in age;
    //@ protected represents age = _age;

    //@ requires g.equals("female")||g.equals("male");
    //@ ensures gender.equals(g) && age == 0;
    public Tortoise(String g) {
        super(g);
        _age = 0;
    }
    
    /*@ also
      @   requires 151<=a && a<=400;    
      @   assignable age;
      @   ensures age == a;          @*/
    public void setAge(int a)
    { if (0 <= a) { _age = a; } }
}
