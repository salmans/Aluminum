package minsolver;

import kodkod.instance.Instance;

public class MinSolutionFactory {
	public static MinSolution satisfiable(MinStatistics stats, Instance instance, int[] propositionalModel){
		return MinSolution.satisfiable(stats, instance, propositionalModel);
	}
}
