public class CallingMethodsExample2 {
	
	//@ spec_public
	final private double FAILINGGRADE = 69.4;
	//@ spec_public
	private int totalFailing = 0;
	public boolean flag;
	
	//@ requires grades != null;
	//@ requires (\forall int i; 0 <= i < grades.length; !Double.isNaN(grades[i]));
	//@ assigns totalFailing;
	public void totalFailing(double[] grades) {
		//int count = 0;
		for(int i = 0; i < grades.length; i++) {
			//@ assume 0 <= i < grades.length;
			if(grades[i] <= FAILINGGRADE) {
				//@ assume 0 <= totalFailing+1 < Integer.MAX_VALUE;
				totalFailing++;
			}
		}
	}
	//@ requires grades != null;
	//@ requires grades.length > 0;
	//@ assigns flag;
	public boolean isClassFailing(double[] grades) {
		int classSize = grades.length;

		if((((double)totalFailing) / ((double)classSize)) >= .5){
			flag = true;
			return flag;
		}else {
			flag = false;
			return flag;
		}
	}
	
	public void testClass() {
		double[] classGrades = {71.6, 31.5, 69.5, 69.3, 98.2, 84.3, 102.0};

		totalFailing(classGrades);
		isClassFailing(classGrades);
		//@ assert isClassFailing(classGrades);
	}
	


}
