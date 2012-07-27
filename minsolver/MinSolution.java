package minsolver;
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

import java.util.HashSet;
import java.util.Set;

import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

/**
 * Represents the full solution to a formula:  an
 * instance if the formula is satisfiable or a
 * proof of unsatisfiability if not.
 * 
 * @specfield formula: Formula // the formula being solved
 * @specfield bounds: Bounds // the bounds on the formula
 * @author Emina Torlak
 */
public final class MinSolution implements Comparable<Object>{
	public static final int INCOMPARABLE_TYPE = 3;
	public static final int INCOMPARABLE = 2;
	
	private final Outcome outcome;
	private final MinStatistics stats;
	private final Instance instance;
	private final MinProof proof;	
	/** Stores the propositional model for this solution. 
	 * This field is going to be used for lifting opratins.*/ 
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
	private MinSolution(Outcome outcome, MinStatistics stats, Instance instance, MinProof proof, int[] propositionalModel) {
		assert outcome != null && stats != null;
		this.outcome = outcome;
		this.stats = stats;
		this.instance = instance;
		this.proof = proof;
		this.propositionalModel = propositionalModel;
	}
	
	/**
	 * Returns a new Solution with a SATISFIABLE outcome, given stats and instance.
	 * @return {s: Solution | s.outcome() = SATISFIABLE && s.stats() = stats && s.instance() = instance }
	 */
	static MinSolution satisfiable(MinStatistics stats, Instance instance, int[] propositionalModel) {
		return new MinSolution(Outcome.SATISFIABLE, stats, instance, null, propositionalModel);
	}
	
	/**
	 * Returns a new Solution with a TRIVIALLY_SATISFIABLE outcome, given stats and instance.
	 * @return {s: Solution | s.outcome() = TRIVIALLY_SATISFIABLE && s.stats() = stats && s.instance() = instance }
	 */
	static MinSolution triviallySatisfiable(MinStatistics stats, Instance instance, int[] propositionalModel) {
		return new MinSolution(Outcome.TRIVIALLY_SATISFIABLE, stats, instance, null, propositionalModel);
	}
	
	/**
	 * Returns a new Solution with a UNSATISFIABLE outcome, given stats and proof.
	 * @return {s: Solution | s.outcome() = UNSATISFIABLE && s.stats() = stats && s.proof() = proof }
	 */
	static MinSolution unsatisfiable(MinStatistics stats, MinProof proof, int[] propositionalModel) {
		return new MinSolution(Outcome.UNSATISFIABLE, stats, null, proof, propositionalModel);
	}
	
	/**
	 * Returns a new Solution with a TRIVIALLY_UNSATISFIABLE outcome, given stats and proof.
	 * @return {s: Solution | s.outcome() = TRIVIALLY_UNSATISFIABLE && s.stats() = stats && s.proof() = proof }
	 */
	static MinSolution triviallyUnsatisfiable(MinStatistics stats, MinProof proof, int[] propositionalModel) {
		return new MinSolution(Outcome.TRIVIALLY_UNSATISFIABLE, stats, null, proof, propositionalModel);
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
	public MinProof proof() {
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
	 * Compares two solutions based on the following standard:
	 * if the current object contains something that the other doesn't returns 1.
	 * if the other object contains something that the current object doesn't returns -1.
	 * if they are equal returns 0.
	 * if they both contains something that the other doesn't returns INCOMPARABLE.
	 * finally, if the input is not a MinSolution or Solution, returns INCOMPARABLE_TYPE
	 */
	public int compareTo(Object object) {
		int result = 0;
		
		if(object instanceof MinSolution)
			result = compareInstances(instance, ((MinSolution)object).instance());
		else if(object instanceof Solution)
			result = compareInstances(instance, ((Solution)object).instance());
		else
			result = INCOMPARABLE_TYPE;
		
		return result;
	}
	
	/**
	 * Compares two sets of instances. We use theInstance for the instance in this MinSolution object and
	 * otherInstance for the instance in a comparable object that is being compared with this.
	 * @param theInstance the first instance.
	 * @param otherInstance the second instance.
	 * @return a value between -1 and 2 based on the contract defined by this.compareTo().
	 */
	private int compareInstances(Instance theInstance, Instance otherInstance){
		int result = 0;
		Set<Relation> theRelations = theInstance.relations();
		Set<Relation> otherRelations = otherInstance.relations();
		
		result = compareRelations(theRelations, otherRelations); //If an instance contains a relation that the other one doesn't
		
		
		//TODO this is not the best way of comparing the two instances but it is working for now:
		if(result == 0)
			result = compareTuples(theInstance, otherInstance); //compare the tuples in the relations.
		else if(result == 1){
			result = hasOtherTuples(otherInstance, theInstance) ? INCOMPARABLE : 1;
		}
		else if(result == -1)
			result = hasOtherTuples(theInstance, otherInstance) ? INCOMPARABLE : -1;		

		return result;
	}
	
	/**
	 * Compares two sets of relations.
	 * @param theRelations the first set of relations.
	 * @param otherRelations the second set of relations.
	 * @return a value between -1 and 2 based on the contract defined by this.compareTo()
	 */
	private int compareRelations(Set<Relation> theRelations, Set<Relation> otherRelations){
		int result = 0;
		
		// We are comparing the names of the relations because Kodkod does not provide
		//a way to compare relations.
		Set<String> theRelationNames = new HashSet<String>();
		Set<String> otherRelationNames = new HashSet<String>();

		for(Relation relation: theRelations)
			theRelationNames.add(relation.name());
		for(Relation relation: otherRelations)
			otherRelationNames.add(relation.name());
		
		boolean firstContainsSecond = theRelationNames.containsAll(otherRelationNames);
		boolean secondContainsFirst = otherRelationNames.containsAll(theRelationNames);

		
		if(firstContainsSecond && secondContainsFirst)
			result = 0;		
		else if(firstContainsSecond && !secondContainsFirst)
			result = 1;
		else if(!firstContainsSecond && secondContainsFirst)
			result = -1;
		else if(!firstContainsSecond && !secondContainsFirst)
			result = INCOMPARABLE;
		
		return result;
	}

	/**
	 * Compares two instances that have equal set of relations.
	 * @param theInstance the first instance.
	 * @param otherInstance the second instance.
	 * @return a number between -1 and 2 based on the contract defined by this.compareTo().
	 */
	private int compareTuples(Instance theInstance, Instance otherInstance){
		int result = 0;
		Set<Relation> theRelations = theInstance.relations();
		
		boolean firstContainsSecond = true;
		boolean secondContainsFirst = true;
		
		for(Relation relation: theRelations){
			TupleSet theTuples = theInstance.tuples(relation);
			TupleSet otherTuples = otherInstance.tuples(getRelationByRelationName(otherInstance, relation.name()));
			
			// We compare tuples by their string representations. The original Tuple.equals() method forces the two tuples to be drawn
			//from the same universe but this is not always what we want.
			Set<String> theTupleNames = new HashSet<String>();
			Set<String> otherTupleNames = new HashSet<String>();
						
			for(Tuple tuple: theTuples) theTupleNames.add(tuple.toString());
			for(Tuple tuple: otherTuples) otherTupleNames.add(tuple.toString());

			if(firstContainsSecond) firstContainsSecond = theTupleNames.containsAll(otherTupleNames);
			if(secondContainsFirst) secondContainsFirst = otherTupleNames.containsAll(theTupleNames);
			
			if(!firstContainsSecond && !secondContainsFirst)
				break;
		}
		
		
		if(firstContainsSecond && secondContainsFirst)
			result = 0;
		else if (!firstContainsSecond && secondContainsFirst)
			result = -1;
		else if (firstContainsSecond && !secondContainsFirst)
			result = 1;
		else if(!firstContainsSecond && !secondContainsFirst)
			result = INCOMPARABLE;
		
		return result;
	}

	/**
	 * Returns true if firstInstance contains tuples that secondInstance doesn't. Otherwise, returns false.
	 * This method assumes that secondInstance has all the relations in firstInstance.
	 * @param theInstance the first instance.
	 * @param otherInstance the second instance.
	 */
	private boolean hasOtherTuples(Instance firstInstance, Instance secondInstance){
		Set<Relation> firstRelations = firstInstance.relations();
		
		boolean tuplesFound = false;
		
		for(Relation relation: firstRelations){
			TupleSet firstTuples = firstInstance.tuples(relation);
			TupleSet secondTuples = secondInstance.tuples(getRelationByRelationName(secondInstance, relation.name()));
			
			// We compare tuples by their string representations. The original Tuple.equals() method forces the two tuples to be drawn
			//from the same universe but this is not always what we want.
			Set<String> firstTupleNames = new HashSet<String>();
			Set<String> secondTupleNames = new HashSet<String>();
						
			for(Tuple tuple: firstTuples) firstTupleNames.add(tuple.toString());
			for(Tuple tuple: secondTuples) secondTupleNames.add(tuple.toString());

			if(!secondTupleNames.containsAll(firstTupleNames)){
				tuplesFound = true;
				break;
			}
		}
		
		return tuplesFound;
	}	
	
	/**
	 * Returns a relation in a given instance by the relation's name.
	 * @param instance the instance containing the relation.
	 * @param relationName the relation name
	 * @return the relation with the given name. It returns "null" if the relation does not exist.
	 */
	private Relation getRelationByRelationName(Instance instance, String relationName){
		Relation result = null;
		
		for(Relation relation: instance.relations()){
			if(relation.name().equals(relationName)){
				result = relation;
				break;
			}
		}
		
		return result;
	}
}