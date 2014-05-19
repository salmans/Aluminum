package minalloy;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import minkodkod.MinSolution;
import minkodkod.MinSolutionFactory;
import minkodkod.engine.fol2sat.MinSymmetryDetectorDelegate;
import kodkod.ast.Relation;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;

public class IsomorphicSolutionBuilder {
	private static class Permutations{
		/** keeps the index of atoms in this partition in the universe. */
		final int[] atoms;
		/** stores the permutations of the atoms in this partition. */
		final int[][] permutations;
		
		Permutations(IntSet intSet){
			atoms = new int[intSet.size()];
			IntIterator iterator = intSet.iterator();
			
			int counter = 0;
			while(iterator.hasNext()) {atoms[counter++] = iterator.next();}

			permutations = new int[factorial(atoms.length)][];
			
			permutations[0] = atoms.clone();
			int[] prev = atoms.clone();
			
			counter = 1;
			while(true){
				if(nextPermutation(prev) == false) break;
				permutations[counter++] = prev.clone();
			}
		}
		
		
		/**
		 * A helper function to compute the factorial function.
		 */
		public static int factorial(int input){
			int result = 1;
			for(int i = 2; i <= input; i++) {result = result * i;}
			return result;
		}
		
		/**
		 * Builds the next lexicographically permutation of a given intput. 
		 * It returns false if the input is the last lexicographical element.  
		 */
	    public static boolean nextPermutation(int[] p) {
	        int a = p.length - 2;
	        while (a >= 0 && p[a] >= p[a + 1]) {
	            a--;
	        }
	        if (a == -1) {
	            return false;
	        }
	        int b = p.length - 1;
	        while (p[b] <= p[a]) {
	            b--;
	        }
	        int t = p[a];
	        p[a] = p[b];
	        p[b] = t;
	        for (int i = a + 1, j = p.length - 1; i < j; i++, j--) {
	            t = p[i];
	            p[i] = p[j];
	            p[j] = t;
	        }
	        return true;
	    }
	}

	/**
	 * Builds all the isomorphic solutions for a given set of MinSolution  and a given Bounds
	 * and returns them as a set of MinSolution. 
	 */
	public static Set<MinSolution> getIsomorphicSolutions(MinSolution input, Bounds skolemBounds){
		Set<MinSolution> results = new HashSet<MinSolution>();		
		 				
		int[][] solutionPermutations = getSolutionPermutations(skolemBounds); //get all of the possible permutations										
		
		Universe theUniverse = input.instance().universe();
		final TupleFactory factory = theUniverse.factory();						
		
		//loop through all of the permutations:
		for(int i = 0; i < solutionPermutations.length; i++){
			Instance instance = new Instance(theUniverse); //The new isomorphic instance

			// Insert lower-bounds
			instance = padInstance(instance, skolemBounds);
			
			//loop through all relations of the current instance
			for(Relation r: input.instance().relations()){
				
				// If this is not in the Skolem bounds, it is a "label" relation added
				// after solving. (See A4Solution.rename()). Ignore.
				if(!skolemBounds.relations().contains(r))
					continue;
				
				TupleSet currentTuples = input.instance().tuples(r);
				
				// replace the atoms in the tuples of this relation with the
				// atoms defined by this permutation.
				Set<Tuple> newTupleSet = new HashSet<Tuple>();
				
				for(Tuple tuple: currentTuples)
				{
					List<Object> atoms = new ArrayList<Object>();
					for(int j = 0; j < tuple.arity(); j++){
						int atomIndex = tuple.atomIndex(j);
						int newAtomIndex = solutionPermutations[i][atomIndex];
						atoms.add(skolemBounds.universe().atom(newAtomIndex));
					}

					newTupleSet.add(factory.tuple(atoms)); //build a new tuple set
				}
				if(newTupleSet.size() > 0)
					instance.add(r, factory.setOf(newTupleSet)); //add the new tuple set to the this relation
			}
			MinSolution solution = MinSolutionFactory.satisfiable(input.stats(), instance, input.minimizationHistory, input.getPropositionalModel(), input.isCanonical);
			
			results.add(solution);
		}
		
		//Removing duplicate entries (if a solution uses a subset of atoms in the universe, we may end up building duplicate isomorphic solutions for it):
		Set<MinSolution> noDuplicates = new TreeSet<MinSolution>(new Comparator<MinSolution>() {
	        @Override
	        public int compare(MinSolution sol1, MinSolution sol2) {
	            return SolutionComparator.compare(sol1, sol2);
	        }
	    });
	    
		noDuplicates.addAll(results);
		
		return noDuplicates;
	}
	
	/**
	 * "Pads" the argument instance with the mappings that occur in bounds.lowerBound
	 * but not in the instance. 
	 * @requires instance.relations in bounds.relations
	 * @effects instance.relations' = bounds.relations' &&
	 *          instance.tuples' = bounds.lowerBound ++ instance.tuples
	 * @return instance
	 */	
	public static Instance padInstance(Instance instance, Bounds bounds) {
		for (Relation r : bounds.relations()) {
			if (!instance.contains(r)) {
				instance.add(r, bounds.lowerBound(r));
			}
		}
		for (IntIterator iter = bounds.ints().iterator(); iter.hasNext();) {
			int i = iter.next();
			instance.add(i, bounds.exactBound(i));
		}
		return instance;
	}
	
	/**
	 * Builds all the permutations for producing isomorphic solutions and returns them
	 * as an array of integer arrays. 
	 */
	private static int[][] getSolutionPermutations(Bounds bounds){
		//Get the permutations of the partitions:
		Set<Permutations> symmetryPermutations = getSymmetryPermutations(bounds);
		
		//Building the number of all the possible permutations:
		int totalSolutionPermutations = 1;
		for(Permutations perm: symmetryPermutations){totalSolutionPermutations *= perm.permutations.length;}
		
		//Initializing the result (size = # of permutations * size of the universe)
		int[][] result = new int[totalSolutionPermutations][bounds.universe().size()];
		
		//Fill the result as the product of permutations of the partitions:
		int offset = 1;
		for(Permutations perm: symmetryPermutations){
			for(int i = 0; i < result.length; i++){
				for(int j = 0; j < perm.atoms.length; j++){
					result[i][perm.atoms[j]] = perm.permutations[(i/offset) % perm.permutations.length][j]; 
				}
			}
			
			offset = offset * Permutations.factorial(perm.atoms.length);
		}
		
		return result;
	}
	
	/**
	 * Builds a set of Permutations corresponding to all the permutations within different
	 * symmetry classes. 
	 */
	private static Set<Permutations> getSymmetryPermutations(Bounds bounds){
		Set<Permutations> result = new HashSet<Permutations>();
		
		//Get the symmetry partitions from Kodkod:
		Set<IntSet> symmetries = MinSymmetryDetectorDelegate.partition(bounds);			
		
		//System.out.println("  Detected symmetries: "+symmetries);
		
		//Create a data structure containing the permutations of atoms in each partition:
		for(IntSet set: symmetries){result.add(new Permutations(set));}
		
		return result;
	}
}
