/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package minalloy.translator;

import java.util.Iterator;
import java.util.NoSuchElementException;
import edu.mit.csail.sdg.alloy4.ErrorAPI;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

/** Immutable; represents a collection of Alloy tuples; comparison is by identity rather than by value. */

public final class MinA4TupleSet implements Iterable<MinA4Tuple> {

    /** The Kodkod tupleset. */
    private final TupleSet tuples;

    /** The A4Solution that this came from. */
    private final MinA4Solution sol;

    /** Construct a TupleSet from the kodkod TupleSet, while renaming each atom using the atom2name map in sol.
     * <br> NOTE: caller must ensure the Kodkod tupleset is not modified, since we expect the resulting A4Tupleset to be constant.
     */
    MinA4TupleSet(TupleSet tuples, MinA4Solution sol) {
        this.tuples = tuples;
        this.sol = sol;
    }

    /** Return the underlying Kodkod tupleset. */
    public TupleSet debugGetKodkodTupleset() { return tuples.clone(); }

    /** Returns a read-only iterator that iterates over each tuple in this TupleSet. */
    public Iterator<MinA4Tuple> iterator() {
        return new Iterator<MinA4Tuple>() {
            private final Iterator<Tuple> it = tuples.iterator();
            public final boolean hasNext() { return it.hasNext(); }
            public final MinA4Tuple next() {
                if (!it.hasNext()) throw new NoSuchElementException();
                return new MinA4Tuple(it.next(), sol);
            }
            public final void remove() { throw new UnsupportedOperationException(); }
        };
    }

    /** Returns the arity. */
    public int arity() { return tuples.arity(); }

    /** Returns the number of tuples in this tuple set. */
    public int size() { return tuples.size(); }

    /** Construct a new tupleset as the product of this and that; this and that must be come from the same solution. */
    public MinA4TupleSet product(MinA4TupleSet that) throws ErrorAPI {
        if (sol != that.sol) throw new ErrorAPI("A4TupleSet.product() requires 2 tuplesets from the same A4Solution.");
        return new MinA4TupleSet(tuples.product(that.tuples), sol);
    }

    /** Construct a new tupleset as the union of this and that; this and that must be come from the same solution.
     * Note: if that==null, then the method returns this A4TupleSet as-is. */
    public MinA4TupleSet plus(MinA4TupleSet that) throws ErrorAPI {
        if (that==null) return this;
        if (sol != that.sol) throw new ErrorAPI("A4TupleSet.plus() requires 2 tuplesets from the same A4Solution.");
        if (arity() != that.arity()) throw new ErrorAPI("A4TupleSet.plus() requires 2 tuplesets with the same arity.");
        if (this==that || tuples.size()==0) return that; else if (that.tuples.size()==0) return this; // special short cut
        TupleSet ts = tuples.clone();
        ts.addAll(that.tuples);
        if (tuples.size()==ts.size()) return this;
        if (that.tuples.size()==ts.size()) return that;
        return new MinA4TupleSet(ts, sol);
    }

    /** Construct a new tupleset as the subtraction of this and that; this and that must be come from the same solution.
     * Note: if that==null, then the method returns this A4TupleSet as-is. */
    public MinA4TupleSet minus(MinA4TupleSet that) throws ErrorAPI {
        if (that==null) return this;
        if (sol != that.sol) throw new ErrorAPI("A4TupleSet.minus() requires 2 tuplesets from the same A4Solution.");
        if (arity() != that.arity()) throw new ErrorAPI("A4TupleSet.minus() requires 2 tuplesets with the same arity.");
        if (tuples.size()==0 || that.tuples.size()==0) return this; // special short cut
        TupleSet ts = tuples.clone();
        ts.removeAll(that.tuples);
        if (tuples.size()!=ts.size()) return new MinA4TupleSet(ts, sol); else return this;
    }

    /** Construct a new tupleset as the intersection of this and that; this and that must be come from the same solution. */
    public MinA4TupleSet intersect(MinA4TupleSet that) throws ErrorAPI {
        if (sol != that.sol) throw new ErrorAPI("A4TupleSet.intersect() requires 2 tuplesets from the same A4Solution.");
        if (arity() != that.arity()) throw new ErrorAPI("A4TupleSet.intersect() requires 2 tuplesets with the same arity.");
        if (this.tuples.size()==0) return this; // special short cut
        if (that.tuples.size()==0) return that; // special short cut
        TupleSet ts = tuples.clone();
        ts.retainAll(that.tuples);
        if (tuples.size()!=ts.size()) return new MinA4TupleSet(ts, sol); else return this;
    }

    /** Prints a human-readable description of this TupleSet. */
    @Override public String toString() {
        StringBuilder sb=new StringBuilder("{");
        for(MinA4Tuple t:this) {
            if (sb.length()>1) sb.append(", ");
            sb.append(t);
        }
        return sb.append('}').toString();
    }
}