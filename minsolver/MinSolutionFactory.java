package minsolver;

import minsolver.MinSolution.MinimizationHistory;
import kodkod.instance.Instance;

public class MinSolutionFactory {
	public static MinSolution satisfiable(MinStatistics stats, Instance instance, MinimizationHistory minimizationHistory, int[] propositionalModel){
		return MinSolution.satisfiable(stats, instance, minimizationHistory, propositionalModel);
	}
}
