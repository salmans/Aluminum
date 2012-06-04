package MinSolver;
import java.util.Iterator;

import kodkod.ast.Formula;
import kodkod.instance.Bounds;

public class MinModelManager {
	/**
	 * private instance of the loaded formula.
	 */
	final private Formula formula;
	/**
	 * private instance for the MinSolver being used by this MinModelManager.
	 */
	final private MinSolver solver;
	
	/**
	 * private instance of bounds
	 */
	final private Bounds bounds;
	
	/**
	 * Creates a new instance of MinModelManager;
	 * @param formula the formula for which the models are being created.
	 */
	public MinModelManager(Formula formula, Bounds bounds){
		this.formula = formula;
		this.bounds = bounds;
		this.solver = initSolver();
	}
	
	private MinSolver initSolver(){
		MinSolver theSolver = new MinSolver();
		MyReporter rep = new MyReporter();
		theSolver.options().setFlatten(true);	
		theSolver.options().setSymmetryBreaking(0); // check we get 4 models not 2
		MinSATSolverFactory minimalFactory = new MinSATSolverFactory(rep);		
		theSolver.options().setSolver(minimalFactory);
		
		// tuple in upper bound ---> that tuple CAN appear in the relation
		// tuple in lower bound ---> tuple MUST appear in the relation
		theSolver.options().setReporter(rep);
		
		return theSolver;
	}

	/**
	 * Returns the formula for which the models are being created.
	 * @return the formula
	 */
	public Formula getFormula() {
		return formula;
	}
	
	/**
	 * Returns the set of minimal models for the given formula.
	 * @return the iterator over the models
	 */
	public Iterator<MinSolution> getMinimalModels(){
		return solver.solveAll(formula, bounds);
	}
	
	/**
	 * Returns a set of minimal models for a given model and a lifter.
	 * @param solution the model to lift from. 
TODO	 * @param lifter the lifter
	 * @return
	 */
	public Iterator<MinSolution> getMinimalModels(MinSolution solution){
		return null;
	}
	
	/**
	 * Notes on Backtracking.
	 * Backtracking is an application dependent operation. An application
	 * may push the current SolutionIterator in a stack and backtrack
	 * as required.
	 */
}
