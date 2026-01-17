public class AssertExample2 {

    public int fastmod8_Bad(int num) {
        int i = num & 7;
        //@ assert i == (num % 8);
        return i;
    }
    
    //@ requires num >= 0;
    public int fastmod8_OK(int num) {
        int i = num & 7;
        //@ assert i == (num % 8);
        return i;
    }
}
