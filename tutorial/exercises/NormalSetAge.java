// openjml --esc NormalSetAge.java
public interface NormalSetAge extends Age {
    /*@ normal_behavior
      @   requires 0 <= a && age <= a <= 150;
      @   assignable age;
      @   ensures age == a;    @*/
    public void setAge(int a);
}
