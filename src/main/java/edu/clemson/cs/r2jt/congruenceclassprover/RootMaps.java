/**
 * RootMaps.java
 * ---------------------------------
 * Copyright (c) 2016
 * RESOLVE Software Research Group
 * School of Computing
 * Clemson University
 * All rights reserved.
 * ---------------------------------
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.txt', which is part of this source code package.
 */
package edu.clemson.cs.r2jt.congruenceclassprover;

import java.util.*;

/**
 * Created by Mike on 10/11/2016.
 */
public class RootMaps {

    protected Map<int[], Integer> rootMap;
    private Map<Integer, SortedSet<int[]>> backRootMap;
    private Map<Integer, SortedSet<int[]>> containmentMap;

    public RootMaps() {
        rootMap = new TreeMap<int[], Integer>(new IntArrayComparator());
        backRootMap = new TreeMap<>();
        containmentMap = new TreeMap<>();
    }

    public int associateTerms(int[] term, int root, TermStore ts) {
        /*if (rootMap.containsKey(term)) {
            // still need to update umap
            ts.trie.insertAndMap(term,root);
            return rootMap.get(term);
        }
*/
        if(term[0]==0 && term[1]==term[2]) return 1;
        rootMap.put(term, root);

        for (int i : term) {
            //assert i == ts.getRootForNullary(i) : "incomp subs" + i + "'" + ts.getRootForNullary(i);
            if (!containmentMap.containsKey(i))
                containmentMap.put(i, new TreeSet<>(new IntArrayComparator()));
            containmentMap.get(i).add(term);
        }
        if (!containmentMap.containsKey(root)) containmentMap.put(root, new TreeSet<>(new IntArrayComparator()));
        containmentMap.get(root).add(term);
        if (!backRootMap.containsKey(root)) {
            backRootMap.put(root, new TreeSet<>(new IntArrayComparator()));
        }
        backRootMap.get(root).add(term);
        Stack<Integer> constantMerges = ts.trie.insertAndMap(term,root);
        while(!constantMerges.isEmpty()){
            ts.merge(constantMerges.pop(),constantMerges.pop());
        }
        return 0;
    }

    protected boolean representsTerm(int x) {
        return backRootMap.containsKey(x) && getLowestOrderTerm(x)!=null;
        //return backRootMap.containsKey(x);
    }

    public int replaceSymbol(int orig, int repl, TermStore ts) {
        // This block replaces roots, but only in backRootMap
        if (backRootMap.containsKey(orig)) {
            if (!backRootMap.containsKey(repl)) backRootMap.put(repl, new TreeSet<>(new IntArrayComparator()));
            backRootMap.get(repl).addAll(backRootMap.remove(orig));
        }
        SortedSet<int[]> rootMapKeysToChange = containmentMap.remove(orig);
        if (rootMapKeysToChange == null)
            return 0;
        Stack<Integer> sideEffects = new Stack<>();

        for (int[] toChange : rootMapKeysToChange) {
            if(!rootMap.containsKey(toChange)){ // then this is not a key term in rootmap
                // but it is in containmentMap
                // need to remove it from backMap and containmentMap
                continue;
            }
            ts.trie.remove(toChange);
            int oldRoot = rootMap.remove(toChange);

            int newRoot = (oldRoot == orig) ? repl : oldRoot;
            int[] changed = substitute(toChange, orig, repl,ts);
            /*for(int i: changed){
                assert i == ts.getRootForNullary(i) : "incomp subs" + i + ":" + ts.getRootForNullary(i);
            }*/
            // substitute will have no effect when only the root needs change
            if (rootMap.containsKey(changed)) {
                int oldVal = rootMap.get(changed);
                if (oldVal != newRoot && oldVal != orig) {
                    sideEffects.push(newRoot);
                    sideEffects.push(oldVal);
                }
            }
            else if (ts.retrieveSymbol(changed[0]).m_name.equals("=") && (changed[1] == changed[2])) {
                ts.merge(newRoot,TermStore.defaultSymbols.TRUE.ordinal());
            } else
                associateTerms(changed, newRoot,ts);
        }

        while (!sideEffects.isEmpty()) {
            ts.merge(sideEffects.pop(), ts.getRootForNullary(sideEffects.pop()));
        }
        return 0;
    }

    private int[] substitute(int[] origT, int from, int to, TermStore ts) {
        int[] r = new int[origT.length];
        for (int i = 0; i < origT.length; ++i) {
            if (origT[i] == from)
                r[i] = to;
            else
                r[i] = origT[i];
        }
        // suppose you have + 2 a.  and a -> 1.  then you need to order args.
        if(ts.isCommutative(r[0])) {
            Arrays.sort(r, 1, r.length);
        }
        return r;
    }

    public int[] getLowestOrderTerm(int s) {
        if(backRootMap.containsKey(s)) {
            next:
            for (int[] t : backRootMap.get(s)) {
                if (rootMap.containsKey(t)) {
                    // do not return these: f(_x) : _x
                    for(int i: t){
                        if(i == s) continue next;
                    }
                    return Arrays.copyOf(t, t.length);
                }
            }
        }
        return null;
    }

    public boolean containsTerm(int[] term) {
        return rootMap.containsKey(term);
    }

    public int getRootForTerm(int[] term) {
        return rootMap.get(term);
    }

    public SortedSet<int[]> getTermsForRoot(int root) {
        SortedSet<int[]> rSet = new TreeSet<>(new IntArrayComparator());
        Set<int[]> brm = backRootMap.get(root);
        if(brm==null) return null;
        for(int[] t: brm){
            if(rootMap.containsKey(t)){
                rSet.add(t);
            }
        }
        return rSet;
    }

    public String showRootMap(TermStore ts) {
        String r = "";
        for (Map.Entry<int[], Integer> me : rootMap.entrySet()) {
            String k = "";
            for (int i : me.getKey()) {
                k += ts.symbol_store.get(i).m_name + " ";
                //k += i + " ";
            }
            r += k + ": " + ts.symbol_store.get(me.getValue()).m_name + "\n";
            //r += k + ": " + me.getValue() + "\n";
        }
        return r;
    }
}
