/**
 * TermStore.java
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

import edu.clemson.cs.r2jt.rewriteprover.absyn.PExp;
import edu.clemson.cs.r2jt.rewriteprover.absyn.PSymbol;
import edu.clemson.cs.r2jt.typeandpopulate.MTType;

import java.util.*;

/**
 * Created by Mike on 9/9/2016.
 * <p>
 * Assumptions: variables uniquely named.  No shared variables between clauses.
 * Symbols keyed on name.  Can't have a variable "S", as it could share same key as a program var.
 */
public class TermStore {

    public enum defaultSymbols {
        EQ, TRUE, FALSE
    }

    protected ArrayList<Integer> parray;
    protected RootMaps rootMap;
    protected Map<String, Integer> stringTable;
    protected TrieBasedTermIndex trie;
    List<Clause> workedOff;
    protected Map<Integer, Set<Integer>> woDisjToWoClauseIndex;
    List<Symbol> symbol_store;
    Map<Integer, PSymbol> toStringMap;
    int constCtr = 0;
    int varCtr = 0;

    public TermStore() {
        parray = new ArrayList<>(1024);
        rootMap = new RootMaps();
        stringTable = new HashMap<>();
        symbol_store = new ArrayList<>(1024);
        toStringMap = new HashMap<>(1024);
        trie = new TrieBasedTermIndex(this);
        stringTable.put("=", symbol_store.size());
        addSymbol(new Symbol("=", "B", 2, true, false));
        stringTable.put("true", symbol_store.size());
        addSymbol(new Symbol("true", "B", 0, true, false));
        stringTable.put("false", symbol_store.size());
        addSymbol(new Symbol("false", "B", 0, true, false));

        // TODO: remove this. just here for testing
        stringTable.put("Max_Depth", symbol_store.size());
        addSymbol(new Symbol("Max_Depth", "N", 0, true, false));

        workedOff = new ArrayList<>();
        Clause trueUnitClause = new Clause();
        trueUnitClause.addConclusion(1, true);
        workedOff.add(trueUnitClause);
        woDisjToWoClauseIndex = new TreeMap<>();
        Set<Integer> singSet = new TreeSet<>();
        singSet.add(0);
        woDisjToWoClauseIndex.put(1, singSet);
    }

    private int addSymbol(Symbol s) {
        symbol_store.add(s);
        parray.add(parray.size());
        return parray.size() - 1;
    }

    protected int[] getTermForStringAr(String[] ts) {
        int[] rInt = new int[ts.length];
        for (int i = 0; i < ts.length; i++) {
            rInt[i] = stringTable.get(ts[i]);
        }
        return rInt;
    }

    private int createNewConstant(String t) {
        return addSymbol(new Symbol("_k" + (constCtr++), t, 0, true, false));

    }

    private int createNewVar(String t) {
        return addSymbol(new Symbol("_v" + (varCtr++), t, 0, false, false));
    }

    // req: comb.len >= 2
    public int putCombination(int[] comb) {
        return putCombination(comb, retrieveSymbol(comb[0]).m_type);
    }

    public int putCombination(int[] comb, String t) {
        int len = comb.length;
        int storeIdx = len - 2;
        boolean isVar = false;
        for (int i = 0; i < len; ++i) {
            comb[i] = getRootForNullary(comb[i]);
            if (!symbol_store.get(comb[i]).m_isConstant)
                isVar = true;
        }
        if (comb[0] == 0 && comb[1] == comb[2])
            return 1;
        // sort args if commut
        if (isCommutative(comb[0])) {
            if (comb[1] > comb[2]) {
                int temp = comb[1];
                comb[1] = comb[2];
                comb[2] = temp;
            }
        }
        if (!rootMap.containsTerm(comb)) {
            int rS = isVar ? createNewVar(t) : createNewConstant(t);
            rootMap.associateTerms(comb, rS, this);
            return rS;
        } else
            return rootMap.getRootForTerm(comb);

    }

    // req: s is a valid index
    public int getRootForNullary(int s) {
        int r = parray.get(s);
        if (s == r)
            return s; // s is a root
        if (parray.get(r) == r)
            return r; // parent of s is a root. no need to set anymore
        r = getRootForNullary(r);
        parray.set(s, r);
        return r;
    }

    protected boolean isCommutative(int x) {
        Symbol s = retrieveSymbol(x);
        switch (s.m_name) {
            case "=":
            case "=:B":
            case "+":
            case "+:N":
            case "+:Z":
                return true;
            default:
                return false;
        }
    }

    // p is interpreted as the root of an expression tree.
    public int getSymbol(PSymbol p) {
        if (!stringTable.containsKey(p.getTopLevelOperation())) {
            stringTable.put(p.getTopLevelOperation(), symbol_store.size());
            parray.add(parray.size());
            symbol_store.add(new Symbol(p));
            assert parray.size() == symbol_store.size();
        }
        return getRootForNullary(stringTable.get(p.getTopLevelOperation()
                .toString()));
    }

    public Symbol retrieveSymbol(int s) {
        return symbol_store.get(parray.get(s));
    }

    protected int merge(int i, int j) {
        int ir = getRootForNullary(i);
        int jr = getRootForNullary(j);

        if (ir == jr) return ir;

        Symbol is = symbol_store.get(ir);
        Symbol js = symbol_store.get(jr);
        int par = ir;
        int chi = jr;
        if (is.m_internal != js.m_internal) {
            if (is.m_internal) {
                par = jr;
                chi = ir;
            }
        } else if (is.m_isConstant != js.m_isConstant) {
            if (js.m_isConstant) {
                par = jr;
                chi = ir;
            }
        } else if (ir > jr) {
            par = jr;
            chi = ir;
        }

        parray.set(chi, par);
        if (woDisjToWoClauseIndex.containsKey(chi)) {
            if (!woDisjToWoClauseIndex.containsKey(par)) {
                woDisjToWoClauseIndex.put(par, new HashSet<>());
            }
            for (int idx : woDisjToWoClauseIndex.remove(chi)) {
                workedOff.set(idx, workedOff.get(idx).updatedClause(this));
                if (workedOff.get(idx).disjuncts.contains(par))
                    woDisjToWoClauseIndex.get(par).add(idx);
            }
        }
        if (woDisjToWoClauseIndex.containsKey(-chi)) {
            int negSym = par;
            if (negSym == 1) {
                negSym = -2;
            }
            if (!woDisjToWoClauseIndex.containsKey(-negSym)) {
                woDisjToWoClauseIndex.put(-negSym, new HashSet<>());
            }
            for (int idx : woDisjToWoClauseIndex.remove(-chi)) {
                workedOff.set(idx, workedOff.get(idx).updatedClause(this));
                if (workedOff.get(idx).disjuncts.contains(-negSym))
                    woDisjToWoClauseIndex.get(-negSym).add(idx);
            }
        }

        trie.updateUcollection(chi, par);
        if (toStringMap.containsKey(chi)) {
            toStringMap.put(par, toStringMap.get(chi));
        } else if (toStringMap.containsKey(par)) {
            toStringMap.put(chi, toStringMap.get(par));
        }
        rootMap.replaceSymbol(chi, par, this);
        return par;
    }

    public boolean isVarTerm(int x) {
        return !retrieveSymbol(x).m_isConstant && rootMap.representsTerm(x);
    }

    public boolean isInternalVarTerm(int x) {
        return (isVarTerm(x) && isInternal(x));
    }

    public boolean isInternal(int x) {
        return retrieveSymbol(x).m_internal;
    }

    public boolean isExternalVar(int x) {
        return !retrieveSymbol(x).m_internal && !retrieveSymbol(x).m_isConstant;
    }

    public boolean isExternalConst(int x) {
        return !retrieveSymbol(x).m_internal && retrieveSymbol(x).m_isConstant;
    }
    public boolean isVar(int x) {
        return !retrieveSymbol(x).m_isConstant;
    }

    public boolean isTerm(int x) {
        return rootMap.representsTerm(x);
    }

    private int abs(int i) {
        if (i < 0)
            return -i;
        return i;
    }

    public int getTerm(PSymbol p) {
        if (p.getSubExpressions().size() == 0)
            return getSymbol(p);
        int[] rAr = new int[p.getSubExpressions().size() + 1];
        rAr[0] = getSymbol(p);
        for (int i = 0; i < p.getSubExpressions().size(); ++i) {
            rAr[i + 1] = getTerm((PSymbol) p.getSubExpressions().get(i));
        }
        int rS = putCombination(rAr, p.getType().toString());
        toStringMap.put(rS, p);
        return rS;

    }

    public Clause introduceClause(Collection<PExp> clause) {
        Clause rClause = new Clause();
        for (PExp aDisj : clause) {
            int t;
            if (aDisj.getTopLevelOperation().equals("not")) {
                t = getTerm((PSymbol) aDisj.getSubExpressions().get(0));
                rClause.addPremise(t, retrieveSymbol(t).m_isConstant);
            } else {
                t = getTerm((PSymbol) aDisj);
                rClause.addConclusion(t, retrieveSymbol(t).m_isConstant);
            }

        }
        return rClause;
    }

    public boolean termIsRooted(int[] term) {
        for (int i : term)
            if (getRootForNullary(i) != i)
                return false;
        return true;
    }

    public String termString(int t) {
        return termString(t, new HashSet<>(), new TreeMap<>());
    }

    // return smallest string of elements of external symbols
    public String termString(int t, HashSet<int[]> termsInChain, Map<Integer, String> foundArgs) {
        String rS = "";
        int r = getRootForNullary(t);
        //if (!retrieveSymbol(r).m_internal)
        //    return retrieveSymbol(r).m_name;
        if (!isTerm(r) || !isInternal(r))
            return retrieveSymbol(r).m_name;
        int[] term = null;

        nextterm:
        for (int[] ot : rootMap.getTermsForRoot(r)) {
            for(int i : ot){
                if(i == r) continue nextterm;;
            }
            if (!termsInChain.contains(ot)) {
                term = ot;
                termsInChain.add(ot);
                break;
            }
        }

        if (term != null) {
            //Map<Integer, String> foundArgs = new HashMap<>();
            for (int i : term) {
                if (getRootForNullary(i) != i) {
                    return "UNP";
                }
                Symbol s = retrieveSymbol(i);
                if (s.m_internal && isTerm(i) && i != t) {
                    if (foundArgs.containsKey(i)) {
                        rS += "(" + foundArgs.get(i) + ")";
                    }
                    else {
                        String argName = termString(i, termsInChain, foundArgs);
                        foundArgs.put(i, argName);
                        rS += "(" + argName + ")";
                    }
                } else if (s.m_name.contains(":"))
                    rS += s.m_name.substring(0, s.m_name.indexOf(":")) + " ";
                else rS += s.m_name + " ";
            }
            return rS;
        }
        return symbol_store.get(r).m_name;
    }

    public int termSize(int t){
        return termSizeRec(t, 0);
    }
    // Returns the term with less positions
    private int termSizeRec(int t,int depth) {
        if(depth > 9) return 10;
        int rS = 0;
        int r = getRootForNullary(t);
        if (!retrieveSymbol(r).m_internal)
            return 1;
        int[] term = rootMap.getLowestOrderTerm(r);
        if (term != null) {
            for (int i : term) {
                int ir = getRootForNullary(i);
                Symbol s = retrieveSymbol(ir);
                if (s.m_internal && rootMap.representsTerm(ir) && getRootForNullary(ir)!=r) {
                    int sz = termSizeRec(ir,depth +1);
                    rS += sz;
                }
                else
                    rS += 1;
            }
            return rS;
        }
        return 1;
    }

    public String termString(int[] t) {
        String r = "";
        for(int i: t){
            r += termString(i) + " ";
        }
        return r;
    }

    public String showMergedSymbols() {
        String rS = "";
        for (int i = 0; i < parray.size(); ++i) {
            if (parray.get(i) != i)
                rS +=
                        symbol_store.get(i).m_name + " = "
                                + symbol_store.get(getRootForNullary(i)).m_name
                                + "\n";
            //rS += i + " = " + getRootForNullary(i) + "\n";
        }
        return rS;
    }

    public String toString() {
        String rS = "";
        return rS;
    }

    public String showRootMaps() {
        return rootMap.showRootMap(this);
    }

    public String showSymbolStore() {
        String r = "";
        int i = 0;
        for (Symbol s : symbol_store) {
            r += (i++) + ":" + s.m_name + " ";
        }
        return r + "\n";
    }

    // returns a set of symbols that are subterms that we might need to instantiate
    public void collectSubterms(int t, Set<Integer> col) {
        Symbol s = retrieveSymbol(t);
        Set<int[]> eqTerm = rootMap.getTermsForRoot(t);
        if (s.m_internal && !col.contains(t) && eqTerm != null) {
            col.add(t);
            for (int[] subTerm : eqTerm) {
                int[] sorted = Arrays.copyOf(subTerm, subTerm.length);
                Arrays.sort(sorted);
                int last = -1;
                for (int x : sorted) {
                    if (last != x) {
                        collectSubterms(x, col);
                        last = x;
                    }
                }
            }
        }
        return;
    }
}
