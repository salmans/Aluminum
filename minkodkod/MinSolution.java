package minkodkod;
/* 
 * Kodkod -- Copyright (c) 2005-2007, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

import minalloy.IsomorphicSolutionBuilder;
import kodkod.ast.Relation;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleSet;

/**
 * From Kodkod Javadoc:
 * Represents the full solution to a formula:  an
 * instance if the formula is satisfiable or a
 * proof of unsatisfiability if not.
 * 
 * ALUMINUM: Keep track of statistics on minimization. Also the
 * new sanitizeToBounds() method used for our test cases.
 * 
 */
public final class MinSolution{
	public static class MinimizationHistory{
		public final int reducedElements;
		public final int reducedAttributes;
		public final int reducedRelations;		
		public final int SATSolverInvocations;

		public MinimizationHistory(){
			this.SATSolverInvocations = -1;
			this.reducedElements = -1;
			this.reducedAttributes = -1;
			this.reducedRelations = -1;
		}
				
		public MinimizationHistory(int SATSolverInvocations){
			this.SATSolverInvocations = SATSolverInvocations;
			this.reducedElements = -1;
			this.reducedAttributes = -1;
			this.reducedRelations = -1;
		}
		
		public MinimizationHistory(int SATSolverInvocations, int reducedElements, int reducedAttributes, int reducedRelations){
			this.SATSolverInvocations = SATSolverInvocations;
			this.reducedElements = reducedElements;
			this.reducedAttributes = reducedAttributes;
			this.reducedRelations = reducedRelations;
		}		
	}
	
	private final Outcome outcome;
	private final MinStatistics stats;
	private Instance instance;
	private final Proof proof;
	public final MinimizationHistory minimizationHistory;
	public final boolean isCanonical; 
	
	
	/** Stores the propositional model for this solution. 
	 * This field is going to be used for augmenting operations.*/ 
	private final int[] propositionalModel;

	/**
	 * Returns the propositional model for this solution.
	 */
	public int[] getPropositionalModel() {		
		return propositionalModel;
	}
	
	/**
	 * Constructs a Solution from the given values.
	 * @requires outcome != null && stats != null
	 * @requires outcome = SATISFIABLE || TRIVIALLY_SATISFIABLE => instance != null
	 */
	private MinSolution(Outcome outcome, MinStatistics stats, Instance instance, Proof proof, MinimizationHistory minimizationHistory,int[] propositionalModel, boolean isCanonical) {
		assert outcome != null && stats != null;
		this.outcome = outcome;
		this.stats = stats;
		this.instance = instance;
		this.proof = proof;
		this.propositionalModel = propositionalModel;
		this.minimizationHistory = minimizationHistory;
		this.isCanonical = isCanonical;
	}
	
	/**
	 * Returns a new Solution with a SATISFIABLE outcome, given stats and instance.
	 * @return {s: Solution | s.outcome() = SATISFIABLE && s.stats() = stats && s.instance() = instance }
	 */
	static MinSolution satisfiable(MinStatistics stats, Instance instance, MinimizationHistory minimizationHistory, int[] propositionalModel, boolean isCanonical) {
		return new MinSolution(Outcome.SATISFIABLE, stats, instance, null, minimizationHistory, propositionalModel, isCanonical);
	}
	
	/**
	 * Returns a new Solution with a TRIVIALLY_SATISFIABLE outcome, given stats and instance.
	 * @return {s: Solution | s.outcome() = TRIVIALLY_SATISFIABLE && s.stats() = stats && s.instance() = instance }
	 */
	static MinSolution triviallySatisfiable(MinStatistics stats, Instance instance, MinimizationHistory minimizationHistory, int[] propositionalModel) {
		return new MinSolution(Outcome.TRIVIALLY_SATISFIABLE, stats, instance, null, minimizationHistory, propositionalModel, true);
	}
	
	/**
	 * Returns a new Solution with a UNSATISFIABLE outcome, given stats and proof.
	 * @return {s: Solution | s.outcome() = UNSATISFIABLE && s.stats() = stats && s.proof() = proof }
	 */
	static MinSolution unsatisfiable(MinStatistics stats, Proof proof, MinimizationHistory minimizationHistory, int[] propositionalModel) {
		return new MinSolution(Outcome.UNSATISFIABLE, stats, null, proof, minimizationHistory, propositionalModel, true);
	}
	
	/**
	 * Returns a new Solution with a TRIVIALLY_UNSATISFIABLE outcome, given stats and proof.
	 * @return {s: Solution | s.outcome() = TRIVIALLY_UNSATISFIABLE && s.stats() = stats && s.proof() = proof }
	 */
	static MinSolution triviallyUnsatisfiable(MinStatistics stats, Proof proof, MinimizationHistory minimizationHistory, int[] propositionalModel) {
		return new MinSolution(Outcome.TRIVIALLY_UNSATISFIABLE, stats, null, proof, minimizationHistory, propositionalModel, true);
	}
		
	/**
	 * Returns the outcome of the attempt to find
	 * a model for this.formula.  If the outcome is 
	 * SATISFIABLE or TRIVIALLY_SATISFIABLE, a satisfying 
	 * instance can be obtained by calling {@link #instance()}.
	 * If the formula is UNSATISFIABLE, a proof of unsatisfiability
	 * can be obtained by calling {@link #proof()} provided that
	 * translation logging was enabled and the unsatisfiability was
	 * determined using a core extracting 
	 * {@link kodkod.engine.satlab.SATSolver sat solver}.
	 * Lastly, if the returned Outcome is
	 * or TRIVIALLY_UNSATISFIABLE, a proof of unsatisfiability can
	 * be obtained by calling {@link #proof()} provided that
	 * translation logging was enabled.
	 * @return an Outcome instance designating the 
	 * satisfiability of this.formula with respect to this.bounds
	 */
	public Outcome outcome() {
		return outcome;
	}
	
	/**
	 * Returns a satisfiying instance for this.formula, if the
	 * value returned by {@link #outcome() this.outcome()} is either
	 * SATISFIABLE or TRIVIALLY_SATISFIABLE.  Otherwise returns null.
	 * @return a satisfying instance for this.formula, if one exists.
	 */
	public Instance instance() {
		return instance;
	}

	/**
	 * Returns a proof of this.formula's unsatisfiability if the value 
	 * returned  by {@link #outcome() this.outcome()} is UNSATISFIABLE or
	 * TRIVIALLY_UNSATISFIABLE, translation logging was enabled during solving, 
	 * and a core extracting {@link kodkod.engine.satlab.SATProver sat solver} (if any)
	 * was used to determine unsatisfiability.
	 * Otherwise, null is returned.  
	 * @return a proof of this.formula's unsatisfiability, if  one is available.
	 */
	public Proof proof() {
		return proof;
	}
	
	/**
	 * Returns the statistics gathered while solving
	 * this.formula.
	 * @return the statistics gathered while solving
	 * this.formula.
	 */
	public MinStatistics stats() {
		return stats;
	}
	
	/**
	 * Returns a string representation of this Solution.
	 * @return a string representation of this Solution.
	 */
	public String toString() {
		final StringBuilder b = new StringBuilder();
		b.append("---OUTCOME---\n");
		b.append(outcome);
		b.append("\n");
		if (instance!=null) {
			b.append("\n---INSTANCE---\n");
			b.append(instance);
			b.append("\n");
		}
		if (proof!=null) {
			b.append("\n---PROOF---\n");
			b.append(proof);
			b.append("\n");
		}
		b.append("\n---STATS---\n");
		b.append(stats);
		b.append("\n");
		return b.toString();
	}
	
	/**
	 * Enumerates the possible outcomes of an attempt
	 * to find a model for a FOL formula.
	 */
	public static enum Outcome {
		/** The formula is satisfiable with respect to the specified bounds. */
		SATISFIABLE,
		/** The formula is unsatisfiable with respect to the specified bounds. */
		UNSATISFIABLE,
		/** 
		 * The formula is trivially satisfiable with respect to the specified bounds: 
		 * a series of simple transformations reduces the formula to the constant TRUE. 
		 **/
		TRIVIALLY_SATISFIABLE,
		/**
		 * The formula is trivially unsatisfiable with respect to the specified bounds:
		 * a series of simple transformations reduces the formula to the constant FALSE.  
		 */
		TRIVIALLY_UNSATISFIABLE
	}

	/**
	 * Used to remove labeling relations inserted by Alloy. The underlying instance is 
	 * copied and replaced, including only those relations in the bounds given.
	 * @param skolemBounds
	 */
	public void sanitizeToBounds(Bounds skolemBounds)
	{
		Instance newInstance = new Instance(instance.universe());		
		newInstance = IsomorphicSolutionBuilder.padInstance(newInstance, skolemBounds);
		
		// Should not need to use names, since it is assumed that this bounds 
		// generated this instance.
		for(Relation r : skolemBounds.relations())
		{
			TupleSet currentTuples = instance.tuples(r);
			newInstance.add(r, currentTuples);
		}
		
		instance = newInstance;
	}
}