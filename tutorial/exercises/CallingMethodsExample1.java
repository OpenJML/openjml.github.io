public class CallingMethodsExample1 {

	//@ spec_public
	final private double FAILINGGRADE = 69.4;

	//@ requires grades != null;
	//@ requires (\forall int i; 0 <= i < grades.length; !Double.isNaN(grades[i]));
	//@ pure
	public int totalFailing(double[] grades) {
		int count = 0;
		for(int i = 0; i < grades.length; i++) {
			//@ assume 0 <= i < grades.length;
			if(grades[i] <= FAILINGGRADE) {
				//@ assume 0 <= count+1 < Integer.MAX_VALUE;
				count++;
			}
		}
		return count;
	}
	
	//@ requires grades != null;
	//@ requires (\forall int i; 0 <= i < grades.length; !Double.isNaN(grades[i]));
	//@ requires grades.length > 0;
	//@ pure
	public boolean isClassFailing(double[] grades) {
		int total = totalFailing(grades);
		int classSize = grades.length;

		if((((double)total) / ((double)classSize)) >= .5){
			return true;
		}else {
			return false;
		}
	}
	
	public void testClass() {
		double[] classGrades = {71.6, 31.5, 69.5, 69.3, 98.2, 84.3, 102.0};
		
		isClassFailing(classGrades);
		//@ assert isClassFailing(classGrades);
	}
}
