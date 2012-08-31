package minalloy;

import java.util.HashSet;
import java.util.Set;

import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import minkodkod.MinSolution;

public class SolutionComparator {
	public static final int INCOMPARABLE = 2;
	
	/**
	 * Compares two solutions based on the following standard:
	 * if the theObject contains something that otherObject doesn't returns 1.
	 * if the otherObject contains something that the theObject doesn't returns -1.
	 * if they are equal returns 0.
	 * if they both contains something that the other doesn't returns INCOMPARABLE.
	 */
	public static int compare(MinSolution theSolution, Solution otherSolution) {
		int result = 0;
		
		result = compareInstances(theSolution.instance(), otherSolution.instance());
		
		return result;
	}

	/**
	 * Overloads compare to support comparing to MinSolution instances.
	 */
	public static int compare(MinSolution theSolution, MinSolution otherSolution) {
		int result = 0;
		
		result = compareInstances(theSolution.instance(), otherSolution.instance());
		
		return result;
	}	
	
	/**
	 * Compares two sets of instances. We use theInstance for the instance in this MinSolution object and
	 * otherInstance for the instance in a comparable object that is being compared with this.
	 * @param theInstance the first instance.
	 * @param otherInstance the second instance.
	 * @return a value between -1 and 2 based on the contract defined by this.compareTo().
	 */
	private static int compareInstances(Instance theInstance, Instance otherInstance){
		int result = 0;

		//Set<Relation> theRelations = theInstance.relations();
		//Set<Relation> otherRelations = otherInstance.relations();
		
		// Alloy inserts new relations (that look like Skolem relations) *AFTER*
		// the solver has produced an instance. See the end of A4Solution.rename().
		// Unlike all other relations, 2 instances of the same spec may not share 
		// the same set of these labelling relations. Thus, we need to compare 
		// models on the intersection of their relations only.		
		
		Set<String> theRelationNames = new HashSet<String>();
		Set<String> otherRelationNames = new HashSet<String>();
		for(Relation relation: theInstance.relations())
			theRelationNames.add(relation.name());
		for(Relation relation: otherInstance.relations())
			otherRelationNames.add(relation.name());
		Set<String> relationsToTest = new HashSet<String>();
		for(String relname : theRelationNames)
			if(otherRelationNames.contains(relname))
				relationsToTest.add(relname);
		
		result = compareTuplesOnRelations(theInstance, otherInstance, relationsToTest);
		
		//result = compareRelations(theRelations, otherRelations); //If an instance contains a relation that the other one doesn't
				
		//TODO this is not the best way of comparing the two instances but it is working for now:
		
		// If both have the same relations, compare the tuples:
		/*if(result == 0) {
			result = compareTuples(theInstance, otherInstance); //compare the tuples in the relations.
		}
		// If theInstance had more tuples than otherInstance (1):
		else if(result == 1){
			result = secondContainsFirst(otherInstance, theInstance) ? INCOMPARABLE : 1;
		}
		// If otherInstance had more tuples than otherInstance (-1):
		else if(result == -1){
			result = secondContainsFirst(theInstance, otherInstance) ? INCOMPARABLE : -1;		
		}*/
				
		return result;
	}
	
	/**
	 * Compares two sets of relations.
	 * @param theRelations the first set of relations.
	 * @param otherRelations the second set of relations.
	 * @return a value between -1 and 2 based on the contract defined by this.compareTo()
	 */
/*	private static int compareRelations(Set<Relation> theRelations, Set<Relation> otherRelations){
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
*/
	/**
	 * Compares two instances that have equal set of relations.
	 * @param theInstance the first instance.
	 * @param otherInstance the second instance.
	 * @return a number between -1 and 2 based on the contract defined by this.compareTo().
	 */
	private static int compareTuplesOnRelations(Instance theInstance, Instance otherInstance, Set<String> relNamesToCompare)
	{
		int result = 0;
						
		boolean firstContainsSecond = true;
		boolean secondContainsFirst = true;						
				
		for(String relname : relNamesToCompare)
		{
			Relation theRelation = getRelationByRelationName(theInstance, relname);
			Relation otherRelation = getRelationByRelationName(otherInstance, relname);
					
			TupleSet theTuples = theInstance.tuples(theRelation);
			TupleSet otherTuples = otherInstance.tuples(otherRelation);
								
			// We compare tuples by their string representations. 
			// The original Tuple.equals() method forces the two tuples to be drawn
			// from the same universe but this is not always what we want.
			Set<String> theTupleNames = new HashSet<String>();
			Set<String> otherTupleNames = new HashSet<String>();
						
			for(Tuple tuple: theTuples) theTupleNames.add(tuple.toString());
			for(Tuple tuple: otherTuples) otherTupleNames.add(tuple.toString());

			if(firstContainsSecond) firstContainsSecond = theTupleNames.containsAll(otherTupleNames);
			if(secondContainsFirst) secondContainsFirst = otherTupleNames.containsAll(theTupleNames);												
						
			// Incomparable because of this relation. No need to check any more relations.
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
	/*
	private static boolean secondContainsFirst(Instance firstInstance, Instance secondInstance){
		
		Set<Relation> firstRelations = firstInstance.relations();
		
		for(Relation relation: firstRelations){
			TupleSet firstTuples = firstInstance.tuples(relation);
			TupleSet secondTuples = secondInstance.tuples(getRelationByRelationName(secondInstance, relation.name()));
			
			// We compare tuples by their string representations. The original Tuple.equals() method forces the two tuples to be drawn
			//from the same universe but this is not always what we want.
			Set<String> firstTupleNames = new HashSet<String>();
			Set<String> secondTupleNames = new HashSet<String>();
						
			for(Tuple tuple: firstTuples) firstTupleNames.add(tuple.toString());
			for(Tuple tuple: secondTuples) secondTupleNames.add(tuple.toString());
			
			// If we do not have strict containment, the 2nd instance doesn't contain the first.
			if(!secondTupleNames.containsAll(firstTupleNames))
				return false;
		}
		
		return true;
	}	*/
	
	/**
	 * Returns a relation in a given instance by the relation's name.
	 * @param instance the instance containing the relation.
	 * @param relationName the relation name
	 * @return the relation with the given name. It returns "null" if the relation does not exist.
	 */
	private static Relation getRelationByRelationName(Instance instance, String relationName){
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
