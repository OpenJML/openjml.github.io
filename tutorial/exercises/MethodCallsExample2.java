public class MethodCallsExample2 {

	//@ requires materialSqFt > 0;
	//@ requires 0 < w <= Integer.MAX_VALUE & 0 < h <= Integer.MAX_VALUE;
	//@ ensures \result <==> (area(w, h) > materialSqFt);
	public boolean enoughMaterial(int materialSqFt, int w, int h) {
		//@ assume materialSqFt > 0 && 0 < w <= Integer.MAX_VALUE & 0 < h <= Integer.MAX_VALUE;
		
		//@ assert 0 < w <= Integer.MAX_VALUE && 0 < h <= Integer.MAX_VALUE;
		int area = area(w, h);
		
		//@ assume area > 0 && area >= w && area >= h;
		
		//@ assert (area > materialSqFt);
		return (area > materialSqFt);	
	}
	
	//@ requires 0 < w <= Integer.MAX_VALUE & 0 < h <= Integer.MAX_VALUE;
	//@ ensures \result > 0;
	//@ ensures \result >= w;
	//@ ensures \result >= h;
	//@ pure
	public int area(int w, int h) {
		//@ assume 0 < w <= Integer.MAX_VALUE & 0 < h <= Integer.MAX_VALUE;
		//@ assume w*h <= Integer.MAX_VALUE;
		int A = w*h;
		
		//@ assert A > 0 && A >= w && A >= h;
		return A;	
	}	

}