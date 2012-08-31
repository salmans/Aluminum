package minkodkod;

/**
 * This class is designed to store other execution options that Aluminum would use independently. 
 */
public class MinExtraOptions {
	//Log the number of elements, attributes and relations that are being reduced by minimization:
	private boolean logMinimizationHistory = false;
	
	public void setLogMinimizationHistory(boolean logMinimizationHistory){
		this.logMinimizationHistory = logMinimizationHistory;
	}

	public boolean logMinimizationHistory(){
		return this.logMinimizationHistory;
	}
}
