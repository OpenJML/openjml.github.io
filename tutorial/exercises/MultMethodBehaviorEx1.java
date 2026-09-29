// openjml --esc MultMethodBehaviorEx1.java
public class MultMethodBehaviorEx1 {

    public int mean(int sum, int totalNum) {
        if(totalNum == 0) {
            throw new ArithmeticException();
        }
        return sum/totalNum;
    }
}
