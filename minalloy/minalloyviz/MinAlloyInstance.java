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

package minalloy.minalloyviz;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import minalloy.translator.MinA4Solution;
import edu.mit.csail.sdg.alloy4.ConstList;

/** Immutable; represents an Alloy instance that can be displayed in the visualizer.
 *
 * <p><b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class MinAlloyInstance {

   /** The original A4Solution object. */
   final MinA4Solution originalA4; // FIXTHIS: eventually we shouldn't need this field...

   /** If true, it is a metamodel, else it is not a metamodel. */
   public final boolean isMetamodel;

   /** The original filename of the model that generated this instance; can be "" if unknown. */
   public final String filename;

   /** The original command that generated this instance; can be "" if unknown. */
   public final String commandname;

   /** The AlloyModel that this AlloyInstance is an instance of. */
   public final MinAlloyModel model;

   /** Maps each AlloyAtom to the AlloySet(s) it is in; its keySet is considered the universe of all atoms.
    * <br> The constructor ensures every AlloySet here is in model.getSets()
    * <br> Furthermore, every AlloyAtom's type is in model.getTypes()
    * <br> Finally, if an atom A is in a set S, we guarantee that A.type is equal or subtype of S.type
    */
   private final Map<MinAlloyAtom,ConstList<MinAlloySet>> atom2sets;

   /** Maps each AlloyType to the AlloyAtom(s) in that type; it is derived from atom2sets.keySet() directly.
    * <br> Thus, every AlloyType here is in model.getTypes(), and every AlloyAtom here is in atom2sets.keySet()
    * <br> Furthermore, the constructor ensures that if an atom is in a subtype, it is also in the supertype.
    */
   private final Map<MinAlloyType,List<MinAlloyAtom>> type2atoms;

   /** Maps each AlloySet to the AlloyAtom(s) in that set; it is derived from atom2sets directly.
    * <br> Thus, every AlloySet here is in model.getSets(), and every AlloyAtom here is in atom2sets.keySet()
    * <br> Finally, if an atom A is in a set S, we guarantee that A.type is equal or subtype of S.type
    */
   private final Map<MinAlloySet,List<MinAlloyAtom>> set2atoms;

   /** Maps each AlloyRelation to a set of AlloyTuple(s).
    * <br> The constructor ensures every AlloyRelation here is in model.getRelations()
    * <br> Furthermore, every AlloyAtom in every AlloyTuple here is in atom2sets.keySet()
    * <br> Finally, if a tuple T is in a relation R, we guarantee that T is a legal tuple for R
    * (Meaning T.arity==R.arity, and for each i, T.getAtom(i).type is equal or subtype of R.getType(i).)
    */
   private final Map<MinAlloyRelation,Set<MinAlloyTuple>> rel2tuples;

   /** This always stores an empty unmodifiable list of atoms. */
   private static final List<MinAlloyAtom> noAtom = ConstList.make();

   /** This always stores an empty unmodifiable list of sets. */
   private static final List<MinAlloySet> noSet = ConstList.make();

   /** This always stores an empty unmodifiable set of tuples. */
   private static final Set<MinAlloyTuple> noTuple = Collections.unmodifiableSet(new TreeSet<MinAlloyTuple>());

   /** Create a new instance.
    *
    * @param filename - the original filename of the model that generated this instance; can be "" if unknown
    * @param commandname - the original command that generated this instance; can be "" if unknown
    * @param model - the AlloyModel that this AlloyInstance is an instance of
    * @param atom2sets - maps each atom to the set(s) it is in; its KeySet is considered the universe of all atoms
    * @param rel2tuples - maps each relation to the tuple(s) it is in
    * <p>
    * (The constructor will ignore any atoms, sets, types, and relations not in the model. So there's no need
    * to explicitly filter them out prior to passing "atom2sets" and "rel2tuples" to the constructor.)
    */
   public MinAlloyInstance(MinA4Solution originalA4, String filename, String commandname, MinAlloyModel model,
         Map<MinAlloyAtom,Set<MinAlloySet>> atom2sets, Map<MinAlloyRelation,Set<MinAlloyTuple>> rel2tuples, boolean isMetamodel) {
      this.originalA4 = originalA4;
      this.filename = filename;
      this.commandname = commandname;
      this.model = model;
      this.isMetamodel=isMetamodel;
      // First, construct atom2sets (Use a treemap because we want its keyset to be sorted)
      {
         Map<MinAlloyAtom,ConstList<MinAlloySet>> a2s = new TreeMap<MinAlloyAtom,ConstList<MinAlloySet>>();
         for(Map.Entry<MinAlloyAtom,Set<MinAlloySet>> e:atom2sets.entrySet()) {
            MinAlloyAtom atom=e.getKey();
            if (!model.hasType(atom.getType())) continue; // We discard any AlloyAtom whose type is not in this model
            // We discard any AlloySet not in this model; and we discard AlloySet(s) that don't match the atom's type
            List<MinAlloySet> sets=new ArrayList<MinAlloySet>();
            for(MinAlloySet set:e.getValue())
               if (model.getSets().contains(set) && model.isEqualOrSubtype(atom.getType(), set.getType()))
                  sets.add(set);
            Collections.sort(sets);
            a2s.put(atom, ConstList.make(sets));
         }
         this.atom2sets = Collections.unmodifiableMap(a2s);
      }
      // Next, construct set2atoms
      {
         Map<MinAlloySet,List<MinAlloyAtom>> s2a = new LinkedHashMap<MinAlloySet,List<MinAlloyAtom>>();
         for(Map.Entry<MinAlloyAtom,ConstList<MinAlloySet>> e:this.atom2sets.entrySet()) for(MinAlloySet set:e.getValue()) {
            List<MinAlloyAtom> atoms=s2a.get(set);
            if (atoms==null) {atoms=new ArrayList<MinAlloyAtom>(); s2a.put(set,atoms);}
            atoms.add(e.getKey());
         }
         for(MinAlloySet set:model.getSets()) {
            List<MinAlloyAtom> atoms=s2a.get(set);
            if (atoms==null) continue;
            Collections.sort(atoms);
            s2a.put(set, Collections.unmodifiableList(atoms));
         }
         this.set2atoms = Collections.unmodifiableMap(s2a);
      }
      // Next, construct type2atoms
      {
         Map<MinAlloyType,List<MinAlloyAtom>> t2a = new LinkedHashMap<MinAlloyType,List<MinAlloyAtom>>();
         for(MinAlloyAtom a: this.atom2sets.keySet()) {
            for(MinAlloyType t=a.getType(); t!=null; t=model.getSuperType(t)) {
               List<MinAlloyAtom> atoms=t2a.get(t);
               if (atoms==null) { atoms=new ArrayList<MinAlloyAtom>(); t2a.put(t,atoms); }
               atoms.add(a);
            }
         }
         for(MinAlloyType t:model.getTypes()) {
            List<MinAlloyAtom> atoms=t2a.get(t);
            if (atoms==null) continue;
            Collections.sort(atoms);
            t2a.put(t, Collections.unmodifiableList(atoms));
         }
         this.type2atoms = Collections.unmodifiableMap(t2a);
      }
      // Finally, construct rel2tuples
      Map<MinAlloyRelation,Set<MinAlloyTuple>> r2t = new LinkedHashMap<MinAlloyRelation,Set<MinAlloyTuple>>();
      for(Map.Entry<MinAlloyRelation,Set<MinAlloyTuple>> e:rel2tuples.entrySet()) {
         MinAlloyRelation rel=e.getKey();
         if (!model.getRelations().contains(rel)) continue; // We discard any AlloyRelation not in this model
         Set<MinAlloyTuple> tuples=new TreeSet<MinAlloyTuple>();
         for(MinAlloyTuple tuple:e.getValue()) {
            if (tuple.getArity()!=rel.getArity()) continue; // The arity must match
            for(int i=0; ; i++) {
               if (i==tuple.getArity()) { tuples.add(tuple); break; }
               MinAlloyAtom a=tuple.getAtoms().get(i);
               if (!this.atom2sets.containsKey(a)) break; // Every atom must exist
               if (!model.isEqualOrSubtype(a.getType(), rel.getTypes().get(i))) break; // Atom must match the type
            }
         }
         if (tuples.size()!=0) r2t.put(rel, Collections.unmodifiableSet(tuples));
      }
      this.rel2tuples = Collections.unmodifiableMap(r2t);
   }

   /** Returns an unmodifiable sorted set of all AlloyAtoms in this AlloyInstance. */
   public Set<MinAlloyAtom> getAllAtoms() { return Collections.unmodifiableSet(atom2sets.keySet()); }

   /** Returns an unmodifiable sorted list of AlloySet(s) that this atom is in; answer can be an empty list. */
   public List<MinAlloySet> atom2sets(MinAlloyAtom atom) {
      List<MinAlloySet> answer=atom2sets.get(atom);
      return answer!=null ? answer : noSet;
   }

   /** Returns an unmodifiable sorted list of AlloyAtom(s) in this type; answer can be an empty list. */
   public List<MinAlloyAtom> type2atoms(MinAlloyType type) {
      List<MinAlloyAtom> answer=type2atoms.get(type);
      return answer!=null ? answer : noAtom;
   }

   /** Returns an unmodifiable sorted list of AlloyAtom(s) in this set; answer can be an empty list. */
   public List<MinAlloyAtom> set2atoms(MinAlloySet set) {
      List<MinAlloyAtom> answer=set2atoms.get(set);
      return answer!=null ? answer : noAtom;
   }

   /** Returns an unmodifiable sorted set of AlloyTuple(s) in this relation; answer can be an empty set. */
   public Set<MinAlloyTuple> relation2tuples(MinAlloyRelation rel) {
      Set<MinAlloyTuple> answer=rel2tuples.get(rel);
      return answer!=null ? answer : noTuple;
   }

   /** Two instances are equal if they have the same filename, same commands,
    * same model, and same atoms and tuples relationships.
    */
   @Override public boolean equals(Object other) {
      if (!(other instanceof MinAlloyInstance)) return false;
      if (other==this) return true;
      MinAlloyInstance x=(MinAlloyInstance)other;
      if (!filename.equals(x.filename)) return false;
      if (!commandname.equals(x.commandname)) return false;
      if (!model.equals(x.model)) return false;
      if (!atom2sets.equals(x.atom2sets)) return false;
      if (!type2atoms.equals(x.type2atoms)) return false;
      if (!set2atoms.equals(x.set2atoms)) return false;
      if (!rel2tuples.equals(x.rel2tuples)) return false; return true;
   }

   /** Computes a hash code based on the same information used in equals(). */
   @Override public int hashCode() {
      int n = 5*filename.hashCode() + 7*commandname.hashCode();
      n = n + 7*atom2sets.hashCode() + 31*type2atoms.hashCode() + 71*set2atoms.hashCode() + 3*rel2tuples.hashCode();
      return 17*n + model.hashCode();
   }

   /** Returns a textual dump of the instance. */
   @Override public String toString() {
      StringBuilder sb=new StringBuilder();
      sb.append("Instance's model:\n");
      sb.append(model.toString());
      sb.append("Instance's atom2sets:\n");
      for(Map.Entry<MinAlloyAtom,ConstList<MinAlloySet>> entry: atom2sets.entrySet()) {
         sb.append("  "); sb.append(entry.getKey()); sb.append(" "); sb.append(entry.getValue()); sb.append('\n');
      }
      sb.append("Instance's rel2tuples:\n");
      for(Map.Entry<MinAlloyRelation,Set<MinAlloyTuple>> entry: rel2tuples.entrySet()) {
         sb.append("  "); sb.append(entry.getKey()); sb.append(" "); sb.append(entry.getValue()); sb.append('\n');
      }
      return sb.toString();
   }
}