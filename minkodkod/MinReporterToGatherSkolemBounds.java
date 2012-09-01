package minkodkod;

import java.util.List;
import java.util.Set;

import kodkod.ast.Decl;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.config.Reporter;
import kodkod.instance.Bounds;
import kodkod.util.ints.IntSet;

/**
 * Implementor of Kodkod's Reporter interface; used to acquire the post-Skolemization
 * Bounds that Kodkod creates internally. Also used to count minimization statistics.
 * @author Tim
 *
 */
public class MinReporterToGatherSkolemBounds implements Reporter
{
	Bounds skolemBounds = null; 
	private int primaryVars;
	private int iterations = 0;
	private int reducedElements = 0;
	private int reducedAttributes = 0;	
	private int reducedRelations = 0;	
	
	@Override
	public void detectedSymmetries(Set<IntSet> parts) {
	}

	@Override
	public void detectingSymmetries(Bounds bounds) {
	}

	@Override
	public void flattening(BooleanFormula circuit) {
	}

	@Override
	public void generatingSBP() {
	}

	@Override
	public void optimizingBoundsAndFormula() {
	}

	@Override
	public void skolemizing(Decl decl, Relation skolem, List<Decl> context) {
		//System.out.println("Reporter: skolemizing: "+ decl +"; "+skolem+";"+context);
	}

	@Override
	public void solvingCNF(int primaryVars, int vars, int clauses) {
		// Make Kodkod tell us how many primary Vars...
		this.primaryVars = primaryVars; 
	}

	@Override
	public void translatingToBoolean(Formula formula, Bounds bounds)
	{		
		// Make kodkod tell us what it's skolemized so we're working with the proper signature/bounds.
		//System.out.println("Reporter: translatingToBoolean: "+ bounds+"==========\n");
		skolemBounds = bounds;		
	}

	@Override
	public void translatingToCNF(BooleanFormula circuit) {				
	}
	
	public void setIterations(int iterations){
		this.iterations = iterations;
	}

	public void setReducedElements(int reducedElements){
		this.reducedElements = reducedElements;
	}

	public void setReducedAttributes(int reducedAttributes){
		this.reducedAttributes = reducedAttributes;
	}

	public void setReducedRelations(int reducedRelations){
		this.reducedRelations = reducedRelations;
	}
	
	public int getIterations(){
		return iterations;
	}	

	public int getReducedElements(){
		return reducedElements;
	}	
	
	public int getReducedAttributes(){
		return reducedAttributes;
	}	
	
	public int getReducedRelations(){
		return reducedRelations;
	}	
	
	int getNumPrimaryVariables()
	{
		return primaryVars;
	}
	
}