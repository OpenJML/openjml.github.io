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
      @   requires age <= a && 151<=a && a<=400;    
      @   assignable age;
      @   ensures age == a;          @*/
    public void setAge(int a)
    {
        if (a < _age) { return; }
        //@ assert age <= a;
        _age = a;
        //@ assert age == a;
    }
}
