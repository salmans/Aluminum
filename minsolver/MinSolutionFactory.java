package minsolver;

import kodkod.instance.Instance;

public class MinSolutionFactory {
	public static MinSolution satisfiable(MinStatistics stats, Instance instance, int SATSolverInvocations, int[] propositionalModel){
		return MinSolution.satisfiable(stats, instance, SATSolverInvocations, propositionalModel);
	}
}
