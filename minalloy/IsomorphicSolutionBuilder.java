package minalloy;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import minsolver.MinSolution;
import minsolver.MinSolutionFactory;
import minsolver.fol2sat.MinSymmetryDetectorDelegate;
import kodkod.ast.Relation;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;

public class IsomorphicSolutionBuilder {
	private static class Permutations{
		final int[] atoms;
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
	public static Set<MinSolution> getIsomorphicSolutions(Set<MinSolution> input, Bounds bounds){
		Set<MinSolution> results = new HashSet<MinSolution>();
		
		int[][] solutionPermutations = getSolutionPermutations(bounds);
		final TupleFactory factory = bounds.universe().factory();
		
		for(MinSolution sol: input){
			for(int i = 0; i < solutionPermutations.length; i++){
				Instance instance = new Instance(bounds.universe());
				instance = padInstance(instance, bounds);
				
				for(Relation r: sol.instance().relations()){
					TupleSet tuples = sol.instance().tuples(r);

					Set<Tuple> tupleSet = new HashSet<Tuple>();
					for(Tuple tuple: tuples){
						List<Object> atoms = new ArrayList<Object>();
						for(int j = 0; j < tuple.arity(); j++){
							int atomIndex = tuple.atomIndex(j);
							int newAtomIndex = solutionPermutations[i][atomIndex];
							atoms.add(bounds.universe().atom(newAtomIndex));
						}
						tupleSet.add(factory.tuple(atoms));
					}
					if(tupleSet.size() > 0)
						instance.add(r, factory.setOf(tupleSet));
				}
				MinSolution solution  = MinSolutionFactory.satisfiable(sol.stats(), instance, sol.getPropositionalModel());
				results.add(solution);
			}
		}
		
		return results;
	}
	
	/**
	 * "Pads" the argument instance with the mappings that occur in bounds.lowerBound
	 * but not in the instance. 
	 * @requires instance.relations in bounds.relations
	 * @effects instance.relations' = bounds.relations' &&
	 *          instance.tuples' = bounds.lowerBound ++ instance.tuples
	 * @return instance
	 */	
	private static Instance padInstance(Instance instance, Bounds bounds) {
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
		Set<Permutations> symmetryPermutations = getSymmetryPermutations(bounds);
		
		int totalSolutionPermutations = 1;
		for(Permutations perm: symmetryPermutations){totalSolutionPermutations *= perm.permutations.length;}
		
		int[][] result = new int[totalSolutionPermutations][bounds.universe().size()];
		
		for(Permutations perm: symmetryPermutations){
			for(int i = 0; i < result.length; i++){
				for(int j = 0; j < perm.atoms.length; j++){
					result[i][perm.atoms[j]] = perm.permutations[i % perm.permutations.length][j]; 
				}
			}
		}
		
		return result;
	}
	
	/**
	 * Builds a set of Permutations corresponding to all the permutations within different
	 * symmetry classes. 
	 */
	private static Set<Permutations> getSymmetryPermutations(Bounds bounds){
		Set<Permutations> result = new HashSet<Permutations>();
		
		Set<IntSet> symmetries = MinSymmetryDetectorDelegate.partition(bounds);
		for(IntSet set: symmetries){result.add(new Permutations(set));}
		
		return result;
	}
}
