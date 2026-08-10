// openjml --esc ExceptionalSetAge.java
public interface ExceptionalSetAge2 extends Age {
    /*@ normal_behavior
      @   requires a < age;
      @   assignable \nothing;
      @   ensures \old(age) == age; @*/
    void setAge(int a); 
}
