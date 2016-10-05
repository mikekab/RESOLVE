package edu.clemson.cs.r2jt.congruenceclassprover;

import edu.clemson.cs.r2jt.collections.*;
import edu.clemson.cs.r2jt.collections.List;
import edu.clemson.cs.r2jt.misc.Utils;

import java.util.*;
import java.util.Iterator;
import java.util.Map;
import org.apache.commons.collections4.trie.*;

/**
 * Created by Mike on 9/22/2016.
 */
public class TermIndex {
    TermStore termStore;
    int arity;
    /*
    all terms are of the same arity.  all arguments are nullary.

     */
    private class Substitution {
        // int[position][symbol ref(s)]
        // pos 0: the whole term, 1: the func symbol, 2+: the args
        Map<Integer, int[]> substitution;
        Set<Integer> varsOfCodomain;

        public Substitution(Map<Integer, int[]> s) {
            substitution = s;
            varsOfCodomain = new HashSet<>();
            for (int[] t : getCodomain()) {
                for (int i = 0; i < t.length; ++i) {
                    int k = t[i];
                    if (k < 0 || !termStore.retrieveSymbol(k).m_isConstant) varsOfCodomain.add(k);
                }
            }
        }

        public Set<Integer> getDomain() {
            Iterator<Map.Entry<Integer, int[]>> mit = substitution.entrySet().iterator();
            while (mit.hasNext()) {
                Map.Entry<Integer, int[]> me = mit.next();
                if (me.getValue().length == 1 && me.getKey() == me.getValue()[0]) {
                    mit.remove();
                }
            }
            return substitution.keySet();
        }

        public int[] get(int k) {
            return substitution.get(k);
        }

        public boolean containsKey(int i) {
            return substitution.containsKey(i);
        }

        public Set<int[]> getCodomain() {
            getDomain();
            Set<int[]> rSet = new HashSet<>();
            for (int[] ia : substitution.values()) {
                rSet.add(ia);
            }
            return rSet;
        }

        public int[] applySubsToTerm(int[] term) {
            int[] ra = new int[term.length];
            for (int i = 0; i < ra.length; ++i) {
                if (substitution.containsKey(term[i])) {
                    assert substitution.get(i).length == 1;
                    ra[i] = substitution.get(i)[0];
                } else
                    ra[i] = term[i];
            }
            return ra;
        }
    }

    private class SubsNode {
        Substitution m_sub; // label
        java.util.List<SubsNode> children;

        public SubsNode(Substitution s) {
            m_sub = s;
            children = new ArrayList<>();
        }

        public boolean isEmpty() {
            if (m_sub.getDomain().isEmpty()) {
                return true;
            }
            return false;
        }
    }

    public TermIndex(TermStore ts, int ar) {
        termStore = ts;
        arity = ar;
    }

    public Substitution composeSubstitutions(Substitution a, Substitution b) {
        Map<Integer, int[]> smap = new HashMap<>();
        for (Integer i : b.getDomain()) {
            smap.put(i, a.applySubsToTerm(b.get(i)));
        }
        for (Integer i : a.getDomain()) {
            if (!b.containsKey(i)) {
                smap.put(i, a.get(i));
            }
        }
        return new Substitution(smap);
    }

    public Substitution normalizeSubstitution(Substitution s){
        Set<Integer> vCo = s.varsOfCodomain;
        Integer[] vCoA = vCo.toArray(new Integer[vCo.size()] );
        Arrays.sort(vCoA);
        assert vCoA[0] >= 0;
        // assumption: no indicator variables in codomain
        Map<Integer,int[]> repMap = new HashMap<>();
        int k = 0;
        for(int i: vCoA){
            repMap.put(i,new int[]{--k});
        }
        Substitution subMap = new Substitution(repMap);
        Map<Integer, int[]> norm = new HashMap<>();
        for(int i: s.getDomain()){
            int[] replacementTerm = subMap.applySubsToTerm(s.get(i));
            norm.put(i,replacementTerm);
        }
        return new Substitution(norm);
    }
    public Substitution joinSubstitutions(Substitution a, Substitution b) {
        Map<Integer, int[]> smap = new HashMap<>();
        for (Integer i : b.getDomain()) {
            smap.put(i, a.applySubsToTerm(b.get(i)));
        }
        for (Integer i : a.getDomain()) {
            if (!b.varsOfCodomain.contains(i)) {
                smap.put(i, a.get(i));
            }
        }
        return new Substitution(smap);
    }

    public boolean is_variantNode(Substitution nLabel, Substitution s) {
        for (int v : nLabel.getDomain()) {
            int[] t = nLabel.get(v);
            if (t.length > 1 || t[0] < 0) return false;
        }
        return true;
    }

    public SubsNode insert(SubsNode n, Substitution s, int[] openVars) {
        if (n.isEmpty()) {
            return new SubsNode(s);
        }
        //if (is_variantNode(n.m_sub, s))
        return null;

    }

}
