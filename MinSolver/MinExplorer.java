package MinSolver;

import java.util.HashMap;
import java.util.Map;

import kodkod.ast.Relation;
import kodkod.engine.fol2sat.Translation;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;

import org.sat4j.core.VecInt;
import org.sat4j.specs.IteratorInt;

public class MinExplorer {	
	//These functions are used for translation purposes:
	public static Instance translatePropositions(Translation translation, Bounds bounds, VecInt theVars)
			//throws MInternalNoBoundsException
	{
		// This function demonstrates how to convert a set of primary propositional
		// variables into set of relational expressions.
		
		// Populate an empty instance over the universe we're using:
		Instance result = new Instance(bounds.universe());
		
				
		// We can get the vars for each relation
		//theTranslation.primaryVariables(relation);
		//theTranslation.numPrimaryVariables()
		//theBounds.relations()

		//////////////////////////////////////////////////////////////////////////
		// Very inefficient! Cache this later. Do in advance of this function!!!
		// E.g. map 158 ---> R if 158 represents <tup> in R for some <tup>.
		Map<Integer, Relation> mapVarToRelation = new HashMap<Integer, Relation>(); 
		for(Relation r : bounds.relations())
		{
			IntSet varsForThisRelation = translation.primaryVariables(r);
			IntIterator itVarsForThis = varsForThisRelation.iterator();
			while(itVarsForThis.hasNext())
			{
				mapVarToRelation.put(itVarsForThis.next(), r);
			}
				
		}
		//////////////////////////////////////////////////////////////////////////
		
		// Now that we have the mapping from var --> its relation, we can find the tuple:
		//Salman: Is there any reason that SAT4J does not use the standard Java iterator?
		//Maybe there are performance issues with that!
		IteratorInt it = theVars.iterator();
		
		while(it.hasNext())
		{			
			int theVar = it.next();
			Relation myRelation = mapVarToRelation.get(theVar);
			IntSet s = translation.primaryVariables(myRelation);		
			Tuple myTuple = getTupleForPropVariable(
						bounds, translation, s, myRelation, theVar);
				
			// .add here is actually .set -- it overwrites what is already in the relation.
			// So we CANNOT just do:			
			//result.add(myRelation, bounds.universe().factory().setOf(myTuple));
			
			TupleSet currentContents = result.tuples(myRelation);
			TupleSet theContents = bounds.universe().factory().setOf(myTuple);
			if(currentContents != null) // returns null instead of empty set!!
				theContents.addAll(currentContents); 
			
			result.add(myRelation, theContents);
		}
		
		
		// Set<RelationalFact> would be better than Instance. But for now use Instance
		
		// Return an instance (should not be interpreted as a model of the qry!!) that contains
		// only those relational facts indicated by theVars
		return result;				
	}

	
	private static Tuple getTupleForPropVariable(Bounds theBounds, Translation theTranslation, IntSet s, Relation r, int theVar)
	//throws MInternalNoBoundsException
	{		        
		// The relation's upper bound has a list of tuple indices. The "index" variable below is an index
		// into that list of indices. (If our upper bound was _everything_, would be no need to de-reference.)
		
        int minVarForR = s.min();    	
		
		// Compute index: (variable - minvariable) of this relation's variables 
        int index = theVar - minVarForR;                            
                                
        // OPT: How slow is this? May want to cache...
        int[] arr = theBounds.upperBound(r).indexView().toArray();
        
        TupleFactory factory = theBounds.universe().factory();   
        Tuple tup = factory.tuple(r.arity(), arr[index]);  

        //MCommunicator.writeToLog("\ngetTupleForPropVariable: thisTuple="+tup+" for "+theVar+". Relation had vars: "+s+" and the offset was "+minVarForR+
        //		"leaving index="+index+". Upper bound indexview: "+Arrays.toString(arr)+
        //		"\nThe de-referenced tuple index is: "+arr[index]);

        
        return tup;
	}	
}
