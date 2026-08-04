public class Tortoise2 implements NormalSetAge {
    protected int _age; //@ in age;
    //@ protected represents age = _age;

    //@ ensures age == 0;
    public Tortoise2() {
        _age = 0;
    }
    
    /*@ also
      @   requires 151<=a && a<=400;    
      @   assignable age;
      @   ensures age == a;          @*/
    public void setAge(int a)
    { if (0 <= a) { _age = a; } }
}
