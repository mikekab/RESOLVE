/**
 * TrieBasedTermIndex.java
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

import org.omg.PortableInterceptor.INACTIVE;

import java.util.*;

/**
 * Created by Mike on 10/4/2016.
 */

public class TrieBasedTermIndex {

    public List<Node> m_roots;
    private TermStore m_termStore;
    private Map<String, Integer> typeMap;
    private Map<Integer, String> backTypeMap;
    private Map<Integer, Map<Integer, List<Map<Integer, Integer>>>> ucollection;// umap(key,val)
    private Map<Integer, Map<Integer, String>> unifStrings;
    private Set<Integer> equations;
    private Map<String, String> subTypeMap;
    private String unifString = "";

    public TrieBasedTermIndex(TermStore ts) {
        m_roots = new ArrayList<>();
        m_termStore = ts;
        typeMap = new HashMap<>();
        backTypeMap = new HashMap<>();
        ucollection = new TreeMap<>();
        subTypeMap = new HashMap<>();
        subTypeMap.put("Prime_Str", "SStr");
        subTypeMap.put("Str('Entry')", "SStr");
        subTypeMap.put("SStr", "Str('Entry')");
        subTypeMap.put("N", "Z");
        unifStrings = new HashMap<>();


    }

    protected void updateUcollection(int orig, int over) {
        if (ucollection.containsKey(orig))
            ucollection.remove(orig);
    }

    private Stack<Integer> umapInsert(int[] term, int root) {
        Stack<Integer> constantMerges = new Stack<>();
        if (term[0] == 0 && term[1] == term[2]) return constantMerges;
        if (!m_termStore.termIsRooted(term)) return constantMerges;
        term = Arrays.copyOf(term, term.length);
        // for each atom unifiable with term
        Node r = m_roots.get(term.length - 1);
        String insTerm = termString(term);
        //System.err.println(test + m_termStore.retrieveSymbol(root).m_name);
        Set<int[]> unifiables = findUnifiableTerms(r, normalizeTerm(term), term, 0);
        // ex. term is reverse k2, root is k51
        // unif is reverse prime, unifroot is  prime
        for (int[] unif : unifiables) {
            if (Arrays.equals(unif, term)) continue;
            if (!m_termStore.rootMap.containsTerm(unif) || !m_termStore.termIsRooted(unif)) {
                remove(unif);
                continue;

            }
            int unifRoot = m_termStore.rootMap.getRootForTerm(unif);


            if (root == unifRoot) continue;
            String unifTerm = m_termStore.termString(unif);
            Map<Integer, Integer> u = unify(term, unif, new TreeMap<>());
            String rstr = m_termStore.retrieveSymbol(root).m_name;
            String uffstr = m_termStore.retrieveSymbol(unifRoot).m_name;

            if (u == null) {
                continue;
                /*throw new
                        RuntimeException("\nunable to unify:" + "\n" +
                        m_termStore.termString(term) + "\n" + m_termStore.termString(unif));*/
            }
            // apply u to root and unifroot
            int nroot = root;
            // nroot is k51, u is prime -> k_2
            if (u.containsKey(nroot)) nroot = u.get(nroot);
            if (u.containsKey(unifRoot)) unifRoot = u.get(unifRoot);
            // unifroot is k_2, was prime
            String rstr2 = m_termStore.retrieveSymbol(nroot).m_name;
            String uffstr2 = m_termStore.retrieveSymbol(unifRoot).m_name;
            if (nroot == unifRoot) continue;
            if (u != null && !u.isEmpty()) {
                // umap(root,unifRoot) = {}+unify(unif,term)
                if (doConstantMerge(unifRoot, root, u)) {
                    constantMerges.push(unifRoot);
                    constantMerges.push(root);
                    continue;
                }
                if (isSubType(unifRoot, nroot)) {
                    assert isSubType(unifRoot, nroot) : m_termStore.termString(unifRoot) + ":" +
                            m_termStore.retrieveSymbol(unifRoot).m_type +
                            " not subtype of " + m_termStore.termString(nroot) + ":" + m_termStore.retrieveSymbol(nroot).m_type;

                    if (!ucollection.containsKey(nroot)) {
                        ucollection.put(nroot, new TreeMap<>());
                        unifStrings.put(nroot, new TreeMap<>());
                    }

                    if (!ucollection.get(nroot).containsKey(unifRoot)) {
                        ucollection.get(nroot).put(unifRoot, new ArrayList<>());
                    }
                    ucollection.get(nroot).get(unifRoot).add(u);
                    unifStrings.get(nroot).put(unifRoot, unifString);
                }
                if (isSubType(nroot, unifRoot)) {
                    if (!ucollection.containsKey(unifRoot)) {
                        ucollection.put(unifRoot, new TreeMap<>());
                        unifStrings.put(unifRoot, new TreeMap<>());
                    }

                    if (!ucollection.get(unifRoot).containsKey(nroot)) {
                        ucollection.get(unifRoot).put(nroot, new ArrayList<>());
                    }
                    ucollection.get(unifRoot).get(nroot).add(u);
                    unifStrings.get(unifRoot).put(nroot, unifString);
                }

            }
        }
        return constantMerges;
    }

    private boolean doConstantMerge(int a, int b, Map<Integer, Integer> u) {
        if (m_termStore.retrieveSymbol(a).m_isConstant && m_termStore.retrieveSymbol(b).m_isConstant) {
            for (Map.Entry<Integer, Integer> me : u.entrySet()) {
                if (!(m_termStore.isExternalVar(me.getKey()) && m_termStore.retrieveSymbol(me.getValue()).m_isConstant)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    protected Map<Integer, Integer> prune(Map<Integer, Integer> m) {
        if (m == null) return null;
        Map<Integer, Integer> r = new TreeMap<>();
        for (Map.Entry<Integer, Integer> me : m.entrySet()) {
            if (!m_termStore.isInternal(me.getKey())) {
                r.put(me.getKey(), me.getValue());
            }
        }
        return r;
    }

    protected List<Map<Integer, Integer>> umapGetForEquation(int x) {
        /*
        For disequality = v1 v2 : v3,
        if v1 is internal,
	        retrieve expr. p a1 ... an : v1
	        retrieve u s.t. p u : v2
	        combine v1,v2 with u
         */
        SortedSet<int[]> xChildren = m_termStore.rootMap.getTermsForRoot(x);
        if (xChildren == null || xChildren.isEmpty()) return null;
        List<Map<Integer, Integer>> rList = new ArrayList<>();
        for (int[] xChild : xChildren) {
            if (xChild == null) continue;
            if (xChild[0] != 0) continue;

            for (int i = 1; i < xChild.length; ++i) {
                if (m_termStore.isInternal(xChild[i]) && ucollection.containsKey(xChild[i])) {
                    Map<Integer, List<Map<Integer, Integer>>> um = ucollection.get(xChild[i]);
                    for (int y : um.keySet()) {
                        if (isSubType(xChild[(i + 1) % 2], xChild[i])) {
                            List<Map<Integer, Integer>> us = um.get(y);
                            for (Map<Integer, Integer> u : us) {
                                if (!u.containsKey(x)) {
                                    // TODO: can probably do composition
                                    Map<Integer, Integer> un = new TreeMap<>();
                                    un.putAll(u);
                                    if (m_termStore.isExternalVar(xChild[(i + 1) % 2]) &&
                                            !varOccursInTerm(xChild[(i + 1) % 2], y)) {
                                        un.put(xChild[(i + 1) % 2], y);
                                        rList.add(un);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return rList;
    }

    /*
        // replacement for umapGet + ucollection
        protected List<Map<Integer, Integer>> retrieveUnifiersForRootSymbols(int x, int y){
            boolean xIsTerm = m_termStore.isTerm(x);
            boolean yIsTerm = m_termStore.isTerm(y);
            for(int[] xterm : m_termStore.rootMap.getTermsForRoot(x)){
                Set<int[]> unifTerms = findUnifiableTerms(xterm);
                for(int[] yterm: unifTerms){
                    int r = m_termStore.rootMap.getRootForTerm(yterm);
                    if(r==y){
                        Map<Integer,Integer> u = unify(xterm,yterm,new TreeMap<>());
                    }
                }
            }

        }
    */
    protected List<Map<Integer, Integer>> umapGet(int x, int y) {

        if (m_termStore.getRootForNullary(x) != x) return null;
        if (!m_termStore.rootMap.representsTerm(x)) return null;

        List<Map<Integer, Integer>> r = new ArrayList<>();
        /*if (!ucollection.containsKey(x) && m_termStore.rootMap.representsTerm(x)) {
            for (int[] term : m_termStore.rootMap.getTermsForRoot(x)) {
                Stack<Integer> constantMerges = insertAndMap(term, x);
                while(!constantMerges.isEmpty()){
                    m_termStore.merge(constantMerges.pop(),constantMerges.pop());
                }
            }
        }*/

        if (!ucollection.containsKey(x)) return null;
        if (!ucollection.get(x).containsKey(y)) return null;
        r.addAll(ucollection.get(x).get(y));
        return r;
    }

    protected Map<Integer, List<Map<Integer, Integer>>> umapGetAll(int x) {
        if (m_termStore.rootMap.representsTerm(x)){
            if (!ucollection.containsKey(x) && m_termStore.rootMap.representsTerm(x))
                for (int[] term : m_termStore.rootMap.getTermsForRoot(x)) {
                    Stack<Integer> conMerges = insertAndMap(term, x);
                    while(!conMerges.isEmpty()){
                        m_termStore.merge(conMerges.pop(),conMerges.pop());
                    }
                }

        }
        if (!ucollection.containsKey(x)) return null;
        Map<Integer, List<Map<Integer, Integer>>> rmap = new TreeMap<>();
        for (Integer k : ucollection.get(x).keySet()) {
            List<Map<Integer, Integer>> r = new ArrayList<>();
            r.addAll(ucollection.get(x).get(k));
            rmap.put(k, r);
        }
        return rmap;
    }

    private boolean isGround(int[] term) {
        for (int i : term) {
            if (!m_termStore.retrieveSymbol(i).m_isConstant) {
                return false;
            }
        }
        return true;
    }

    private class Node {

        public SortedSet<int[]> terms;
        public Map<Integer, Node> children; // key is next symbol
        int count; // how many terms use this node

        public Node() {
            children = new TreeMap<>();
            terms = new TreeSet<>(new IntArrayComparator());
            count = 0;
        }
    }

    public boolean contains(int[] term) {
        int sz = term.length;
        if (m_roots.size() < sz) {
            return false;
        }
        Node cur = m_roots.get(sz - 1);
        int[] norm = normalizeTerm(term);
        int idx = 0;
        while (idx < sz) {
            if (cur.children.containsKey(norm[idx])) {
                cur = cur.children.get(norm[idx]);
                ++idx;
            } else
                return false;
        }
        return cur.terms.contains(term);
    }

    public void insert(int[] term) {
        term = Arrays.copyOf(term, term.length);
        if (contains(term))
            remove(term);
        int sz = term.length;
        while (m_roots.size() < term.length) {
            m_roots.add(new Node());
        }
        Node cur = m_roots.get(term.length - 1);
        cur.count = cur.count + 1;
        int[] norm = normalizeTerm(term);
        int idx = 0;
        while (idx < sz) {
            if (cur.children.containsKey(norm[idx])) {
                cur = cur.children.get(norm[idx]);
                cur.count = cur.count + 1;
                ++idx;
            } else
                break;
        }
        while (idx < sz) {
            Node n = new Node();
            cur.children.put(norm[idx], n);
            cur.count = cur.count + 1;
            cur = cur.children.get(norm[idx]);
            idx++;
        }
        cur.count = cur.count + 1;
        cur.terms.add(term);
    }

    public void remove(int[] term) {
        remove_p(term);
        if (m_termStore.isCommutative(term[0])) {
            remove_p(new int[]{term[0], term[2], term[1]});
        }
    }

    private void remove_p(int[] term) {
        if (!contains(term))
            return;
        int sz = term.length;
        if (m_roots.size() < sz)
            return;
        Node cur = m_roots.get(term.length - 1);
        cur.count = cur.count - 1;
        int[] norm = normalizeTerm(term);
        int idx = 0;
        while (idx < sz) {
            if (cur.children.get(norm[idx]).count == 1) {
                cur.children.remove(norm[idx]);
                return;
            }
            cur = cur.children.get(norm[idx]);
            cur.count = cur.count - 1;
            ++idx;

        }
        cur.terms.remove(term);
        cur.count = cur.count - 1;
    }

    private String subsToString(Map<Integer, Integer> subMap) {
        String m = "";
        if (subMap != null) {
            for (Map.Entry<Integer, Integer> e : subMap.entrySet()) {
                if (e.getKey() != m_termStore.getRootForNullary(e.getKey())
                        || e.getValue() != m_termStore.getRootForNullary(e
                        .getValue()))
                    return "Stale Map\n";
                m += m_termStore.termString(e.getKey()) + "\u21d2";
                String longname = m_termStore.termString(e.getValue());
                m += longname + "\n";
            }
        }
        return m;
    }

    private int[] normalizeTerm(int[] term) {
        int[] rA = new int[term.length];
        for (int i = 0; i < term.length; ++i) {
            Symbol s = m_termStore.symbol_store.get(term[i]);
            if (s.m_isConstant) {
                rA[i] = term[i];
            } else {
                if (!typeMap.containsKey(s.m_type)) {
                    int varId = typeMap.size() + 1;
                    typeMap.put(s.m_type, varId);
                    backTypeMap.put(varId, s.m_type);
                }
                rA[i] = -typeMap.get(s.m_type);
            }
        }
        return rA;
    }

    public Set<int[]> findGeneralizations(Node n, int[] key, int pos) {

        Set<int[]> generalizations = new HashSet<>();

        if (n.children.containsKey(key[pos])) {
            if (n.children.get(key[pos]).children.isEmpty()) {
                generalizations.addAll(n.children.get(key[pos]).terms);
            } else generalizations = findGeneralizations(n.children.get(key[pos]), key, pos + 1);
        }
        if (n.children.containsKey(-1)) {
            if (n.children.get(-1).children.isEmpty()) {
                generalizations.addAll(n.children.get(-1).terms);
            } else {
                generalizations.addAll(findGeneralizations(n.children.get(-1), key, pos + 1));
            }
        }
        if (generalizations.contains(key)) generalizations.remove(key);
        return generalizations;
    }

    // is a:type subtype of b:type
    public boolean isSubType(int a, int b) {
        String aT =
                a < 0 ? backTypeMap.get(-a)
                        : m_termStore.retrieveSymbol(a).m_type;
        String bT =
                b < 0 ? backTypeMap.get(-b)
                        : m_termStore.retrieveSymbol(b).m_type;
        if (bT.equals("Entity"))
            return true;
        if (aT.equals(bT))
            return true;
        else if (subTypeMap.containsKey(aT) && subTypeMap.get(aT).equals(bT))
            // else if (subTypeMap.containsKey(bT) && subTypeMap.get(bT).equals(bT))
            return true;
        return false;
    }

    public Set<int[]> findUnifiableTerms(int[] key) {
        Node r = m_roots.get(key.length - 1);
        //System.err.println(test + m_termStore.retrieveSymbol(root).m_name);
        int[] term = Arrays.copyOf(key, key.length);
        return findUnifiableTerms(r, normalizeTerm(term), term, 0);
    }

    private Set<int[]> findUnifiableTerms(Node n, int[] key, int[] notNormalized, int pos) {
        Set<int[]> unifiableTerms = new HashSet<>();
        if (key[pos] < 0) { // explore all children of node that are the same type
            if (pos < key.length - 1) {
                for (Map.Entry<Integer, Node> me : n.children.entrySet()) {
                    if (isSubType(me.getKey(), key[pos])) // if they type of the key at pos is compatible with the type of me.key
                        unifiableTerms.addAll(findUnifiableTerms(me.getValue(), key, notNormalized, pos + 1));
                }
            } else {
                for (Node child : n.children.values())
                    unifiableTerms.addAll(child.terms);
            }

        } else {
            if (n.children.containsKey(key[pos])) {
                if (n.children.get(key[pos]).children.isEmpty()) {
                    unifiableTerms.addAll(n.children.get(key[pos]).terms);
                } else {
                    unifiableTerms = findUnifiableTerms(n.children.get(key[pos]), key, notNormalized, pos + 1);
                }
            }
            // n has a variable child of same type as key at pos
            // key[pos] should be a subtype of the var child
            for (int c : n.children.keySet()) {
                if (c < 0 && isSubType(key[pos], c)) {
                    if (pos < key.length - 1)
                        unifiableTerms.addAll(findUnifiableTerms(n.children.get(c), key, notNormalized, pos + 1));
                    else
                        unifiableTerms.addAll(n.children.get(c).terms);
                }
            }/*
            String keyPosType = m_termStore.retrieveSymbol(key[pos]).m_type;
            if (typeMap.containsKey(keyPosType) &&
                    n.children.containsKey(-typeMap.get(keyPosType))) {
                int varId = -typeMap.get(keyPosType);
                if (pos < key.length - 1)
                    unifiableTerms.addAll(findUnifiableTerms(n.children.get(varId), key, pos + 1));
                else
                    unifiableTerms.addAll(n.children.get(varId).terms);
            }
            */
        }
        unifiableTerms.remove(notNormalized);
        return filter(notNormalized, unifiableTerms);

    }

    private Set<int[]> filter(int[] searchTerm, Set<int[]> results) {
        Iterator<int[]> it = results.iterator();
        while (it.hasNext()) {
            // throw out, for ex. searchterm = f(x,x), result = f(a,b)
            if (!filterCheck(searchTerm, it.next())) {
                it.remove();
            }
        }
        return results;
    }

    private boolean filterCheck(int[] t, int[] u) {
        Map<Integer, Integer> temp = new HashMap<>();
        for (int i = 0; i < t.length; ++i) {
            if (m_termStore.isVar(t[i])) {
                if (temp.containsKey(t[i]) && temp.get(t[i]) != u[i])
                    return false;
                temp.put(t[i], u[i]);
            }
            if (m_termStore.isVar(u[i])) {
                if (temp.containsKey(u[i]) && temp.get(u[i]) != t[i])
                    return false;
                temp.put(u[i], t[i]);
            }
        }
        return true;
    }

    public Stack<Integer> insertAndMap(int[] term, int root) {

        // for (int i : term)
        //assert m_termStore.getRootForNullary(i) == i : termString(term);
        insert(term);
        //assert m_termStore.getRootForNullary(root) == root;
        Stack<Integer> rStack = umapInsert(term, root);
        if (m_termStore.isCommutative(term[0])) {
            rStack.addAll(umapInsert(new int[]{term[0], term[2], term[1]}, root));
        }
        return rStack;
    }

    private Map<Integer, Integer> makeSubs(int x, int y) {
        Map<Integer, Integer> rMap = new TreeMap<>();
        x = m_termStore.getRootForNullary(x);
        y = m_termStore.getRootForNullary(y);
        if (x == 1) {
            int t = x;
            x = y;
            y = t;
        }
        if (isSubType(x, y))
            rMap.put(x, y);


        else if (isSubType(y, x))
            rMap.put(y, x);

        return rMap;
    }

    private Map<Integer, Integer> combineSubs(Map<Integer, Integer> m,
                                              Map<Integer, Integer> n) {
        if (m == null || n == null)
            return null;
        Map<Integer, Integer> rMap = new TreeMap<>();
        rMap.putAll(m);
        for (Map.Entry<Integer, Integer> ne : n.entrySet()) {
            if (m.containsKey(ne.getKey())) {
                if (m.get(ne.getKey()).equals(ne.getValue()))
                    continue;
                else
                    return null;
            } else if (isSubType(ne.getValue(), ne.getKey())) {
                rMap.put(ne.getKey(), ne.getValue());
            } else {
                return null; // maybe flip kv
            }
        }
        return rMap;
    }


    private Map<Integer, Integer> composeSubs(Map<Integer, Integer> m, Map<Integer, Integer> n) {
        Map<Integer, Integer> rMap = new TreeMap<>();
        for (Map.Entry<Integer, Integer> me : m.entrySet()) {
            //int rk = n.containsKey(me.getKey()) ? n.get(me.getKey()) : me.getKey();
            //int rv = n.containsKey(me.getValue()) ? n.get(me.getValue()) : me.getValue();
            int rk = me.getKey();
            while (n.containsKey(rk)) {
                rk = n.get(rk);
            }
            int rv = me.getValue();
            while (n.containsKey(rv)) {
                rv = n.get(rv);
            }
            if (rk == rv) continue;
            if (rMap.containsKey(rk) && !rMap.get(rk).equals(rv)) {
                return null;
            }
            rMap.put(rk, rv);
        }
        // rMap contains entries in m changed by n
        for (Map.Entry<Integer, Integer> ne : n.entrySet()) {
            if (rMap.containsKey(ne.getKey()) && rMap.get(ne.getKey()) != ne.getValue())
                return null;
            rMap.put(ne.getKey(), ne.getValue());
        }
        return rMap;
    }


    private Integer applySubsToSubTerm(int subterm, Map<Integer, Integer> subs) {
        return applySubsToSubTerm(subterm, subs, 0);
    }

    private Integer applySubsToSubTerm(int subterm, Map<Integer, Integer> subs, int depth) {
        if (depth > 5) return null;
        if (subs.containsKey(subterm))
            return subs.get(subterm);
        if (!m_termStore.isInternalVarTerm(subterm))
            return subterm;
        int[] t = m_termStore.rootMap.getLowestOrderTerm(subterm);
        for (int i = 0; i < t.length; ++i) {
            if (m_termStore.isInternalVarTerm(t[i])) {
                Integer n = applySubsToSubTerm(t[i], subs, depth + 1);
                if (n == null)
                    return null;
                t[i] = n;
            } else if (subs.containsKey(t[i])) {
                t[i] = subs.get(t[i]);
            }
        }
        // we have formed a term, but it may not exist
        if (m_termStore.rootMap.containsTerm(t)) {
            return m_termStore.rootMap.getRootForTerm(t);
        }
        return null;
    }


    // req: length a = length b
    // Find a difference, if it can be resolved, map it for return, change the terms, start again
    private Map<Integer, Integer> unify(int[] t1, int[] t2,
                                        Map<Integer, Integer> subs) {
        if (Arrays.equals(t1, new int[]{39, 40}) || Arrays.equals(t2, new int[]{39, 40})) {
            System.out.println();
        }
        if (!m_termStore.rootMap.containsTerm(t1)
                || !m_termStore.rootMap.containsTerm(t2))
            return null;
        int t1R = m_termStore.rootMap.getRootForTerm(t1);
        int t2R = m_termStore.rootMap.getRootForTerm(t2);
        int[] a = Arrays.copyOf(t1, t1.length);
        int[] b = Arrays.copyOf(t2, t2.length);
        for (int i = 0; i < a.length; ++i) {
            if (a[i] == b[i])
                continue;
            // Either return null or change the terms
            int ai = a[i];
            int bi = b[i];
            if (!m_termStore.isVar(ai) && !m_termStore.isVar(bi))
                return null;

            if (m_termStore.isVar(ai) && m_termStore.isVar(bi)) {
                // both vars
                return null;/*
                if (m_termStore.isInternalVarTerm(ai)
                        || m_termStore.isInternalVarTerm(bi)) {
                    // the idea with this is that the results of the unify function are
                    // stored in umap.  so only extern vars to x get stored there.
                    List<Map<Integer, Integer>> stu = umapGet(ai, bi);
                    if (stu == null)
                        stu = umapGet(bi, ai);
                    if (stu == null)
                        return null;
                    boolean found = false;
                    for (Map<Integer, Integer> st : stu) {
                        Map<Integer, Integer> comb = combineSubs(subs, st);
                        if (comb != null) {
                            subs = comb;
                            found = true;
                            break;
                        }
                    }

                    if (!found)
                        return null;
                }
                // both vars of same type
                else if (isSubType(ai, bi) && isSubType(bi, ai)) {
                    // prefer that key is newer than value
                    if (ai < bi) {
                        int temp = ai;
                        ai = bi;
                        bi = temp;
                    }
                    if (!varOccursInTerm(ai, bi)) {
                        subs.put(ai, bi);
                        //a[i] = b[i];
                    } else if (!varOccursInTerm(bi, ai)) {
                        subs.put(bi, ai);
                        //b[i] = a[i];
                    } else {
                        return null;
                    }
                } else { // both vars, one is strict subtype of other
                    // not sure if this works with composition, so disabling it altogether
                    //return null;
                    if (isSubType(ai, bi) && !varOccursInTerm(bi, ai)) { // all of type a is in type b
                        subs.put(bi, ai);
                    } else if (isSubType(bi, ai) && !varOccursInTerm(ai, bi)) {
                        subs.put(ai, bi);
                    } else {
                        return null;
                    }
                } */
            } else { // one const, one var
                int var = m_termStore.isVar(ai) ? ai : bi;
                int con = var == ai ? bi : ai;
                if (isSubType(con, var)) {
                    if (m_termStore.isInternalVarTerm(var)) {
                        List<Map<Integer, Integer>> stu = umapGet(var, con);
                        //if (stu == null)
                        //stu = umapGet(bi, ai);
                        if (stu == null)
                            return null;
                        boolean found = false;
                        for (Map<Integer, Integer> st : stu) {
                            Map<Integer, Integer> comb = combineSubs(subs, st);
                            if (comb != null) {
                                subs = comb;
                                found = true;
                                break;
                            }
                        }
                        if (!found)
                            return null;
                    } else if (!subs.containsKey(var)
                            || subs.get(var).equals(con))
                        subs.put(var, con);
                    else
                        return null;
                } else
                    return null;
            }
            // apply subs to both terms and start over.
            for (int j = 0; j < a.length; ++j) {
                Integer aI = applySubsToSubTerm(a[j], subs);
                if (aI == null)
                    return null;
                a[j] = aI;
                Integer bI = applySubsToSubTerm(b[j], subs);
                if (bI == null)
                    return null;
                b[j] = bI;
                if (j <= i && a[j] != b[j])
                    return null;
            }
            //i = -1;
        }
        /* for (int k1 : subs.keySet()) {
             for (int k2 : subs.keySet()) {
                 if (k1 != k2 && m_termStore.isVar(k1) && m_termStore.isTerm(k2))
                     if (varOccursInTerm(k1, k2)) {
                         return null;
                     }
             }
         }*/
        assert Arrays.equals(a, b);
        //if ((t1R == 1 && t2R == 2) || (t2R == 1 && t1R == 2))
        unifString =
                (termString(t1) + ":" + m_termStore.termString(t1R) + "\n"
                        + termString(t2) + ":" + m_termStore.termString(t2R)
                        + "\n" + subsToString(subs));
        for (Map.Entry<Integer, Integer> me : subs.entrySet()) {
            if (varOccursInTerm(me.getKey(), me.getValue())) return null;
        }
        return subs;
    }

    // for each atom a s.t. a:true,
    // for each atom b s.t there exists a unifier u st. a U = b U
    // if aU exists and bU exists, find r1 and r2 s.t. aU:r1 and bU:r2. merge r1
    public String instantiateTrueAtoms() {
        Set<int[]> terms = m_termStore.rootMap.getTermsForRoot(1);
        if (terms == null) return "";
        String r = "";
        for (int[] a : terms) {
            Set<int[]> unifWithSet = findUnifiableTerms(m_roots.get(a.length - 1), normalizeTerm(a), a, 0);
            for (int[] unifWith : unifWithSet) {
                if (Arrays.equals(unifWith, a)) continue;
                Map<Integer, Integer> u = unify(a, unifWith, new TreeMap<>());
                if (u == null) continue;
                int[] subst = doSubs(a, u);
                if (subst == null) continue;

                if (!Arrays.equals(subst, a)) {
                    if (m_termStore.rootMap.containsTerm(subst)) {
                        int oldroot = m_termStore.rootMap.getRootForTerm(subst);
                        if (oldroot != 1) {
                            //r += (termString(a) + "\n" + m_termStore.termString(unifWith) + "\n" + subsToString(u));
                            //r += m_termStore.termString(subst) + "\n";
                            r += "Asserting: " + m_termStore.termString(oldroot) + "\n" + unifString + "\n";
                            m_termStore.merge(1, oldroot);
                        }
                    }
                }
            }
        }
        if (r.equals("")) return "";
        return "\n\nInstantiating true atoms\n" + r;
    }

    private int[] doSubs(int[] a, Map<Integer, Integer> u) {
        int[] rInt = new int[a.length];
        for (int i = 0; i < a.length; ++i) {
            Integer si = applySubsToSubTerm(a[i], u);
            if (si == null)
                return null;
            rInt[i] = si;
        }
        return rInt;
    }

    private boolean varOccursInTerm(int var, int varTerm) {
        if (m_termStore.isVarTerm(varTerm) && m_termStore.isInternal(varTerm)) { // check if var is internal term
            int[] lot = m_termStore.rootMap.getLowestOrderTerm(varTerm);
            if (intArContains(var, lot))
                return true;
            for (int i : lot) {
                if (i == varTerm)
                    continue;
                if (varOccursInTerm(var, i))
                    return true;
            }
        }
        return false;
    }

    private boolean intArContains(int x, int[] a) {
        for (int i = 0; i < a.length; ++i) {
            if (a[i] == x)
                return true;
        }
        return false;
    }

    private String termString(int[] term) {
        String rS = "";
        for (int i = 0; i < term.length; ++i) {
            Symbol is = m_termStore.retrieveSymbol(term[i]);
            if (is.m_internal)
                rS += " (" + m_termStore.termString(term[i]) + ") ";
            else
                rS += m_termStore.retrieveSymbol(term[i]).m_name;
            String sep = i == term.length - 1 ? ")" : ",";
            rS += i == 0 ? "(" : sep;
        }
        return rS;
    }

    public String test() {
        String rS = "";
        int[] t1 =
                m_termStore.getTermForStringAr(new String[]{"<=", "I", "J"});

        Set<int[]> gens = findGeneralizations(m_roots.get(3), t1, 0); // findGeneralization f(x,y). should be 1,2
        for (int[] t : gens) {
            rS += termString(t) + "\n";
        }

        return rS;
    }

    // for each disequality = x y : f, try to unify x, y
    // return first found unifier
    public String contradictDisequalities() {
        Set<int[]> f = m_termStore.rootMap.getTermsForRoot(2);
        String log = "";
        String just = "";
        if (f == null)
            return log;
        if (ucollection.containsKey(2))
            ucollection.get(2).remove(1);
        List<Map<Integer, Integer>> us;
        for (int[] t : f) {
            if (t[0] != 0) {
                umapInsert(t, 2);
                us = umapGet(2, 1);
                if (us != null)
                    just = unifStrings.get(2).get(1);
            } else {
                //System.err.println(m_termStore.termString(t));
                us = umapGet(t[1], t[2]);
                if (us != null)
                    just = unifStrings.get(t[1]).get(t[2]);
                else {
                    us = umapGet(t[2], t[1]);
                    if (us != null)
                        just = unifStrings.get(t[2]).get(t[1]);
                }
            }

            if (us != null) {
                //String ts = m_termStore.termString(t);
                Map<Integer, Integer> u = us.iterator().next();
                log +=
                        "Contradiction found with not(" + termString(t) + ")\n"
                                + subsToString(u) + "\n" + "Unifier:\n" + just
                                + "\n";
                return log;
            }
        }
        return log;
    }
}
