// openjml --esc ExceptionalSetAge.java
public interface ExceptionalSetAge2 extends Age {
    /*@ normal_behavior
      @   requires a < age;
      @   assignable \nothing;
      @*/
    void setAge(int a); 
}
