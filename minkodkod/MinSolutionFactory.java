package minkodkod;

import minkodkod.MinSolution.MinimizationHistory;
import kodkod.instance.Instance;

/**
 * Used by Aluminum's test suite when producing isomorphs.  
 */
public class MinSolutionFactory {
	public static MinSolution satisfiable(MinStatistics stats, Instance instance, MinimizationHistory minimizationHistory, int[] propositionalModel, boolean isCanonical){
		return MinSolution.satisfiable(stats, instance, minimizationHistory, propositionalModel, isCanonical);
	}
}
