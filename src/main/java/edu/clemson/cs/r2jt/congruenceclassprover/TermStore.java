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

    protected ArrayList<Map<int[], int[]>> term_Store; //list of sets. index is arity -1
    protected ArrayList<Integer> parray;
    List<Map<int[], Integer>> rootMap;
    Map<String, Integer> stringTable;
    List<Symbol> symbol_store;
    Map<Integer, PSymbol> toStringMap;
    int constCtr = 0;
    int varCtr = 0;

    public TermStore() {
        term_Store = new ArrayList<>(4);
        parray = new ArrayList<>(1024);
        rootMap = new ArrayList<>();
        stringTable = new HashMap<>();
        symbol_store = new ArrayList<>(1024);
        toStringMap = new HashMap<>(1024);


    }

    private int addSymbol(Symbol s) {
        symbol_store.add(s);
        parray.add(parray.size());
        return parray.size() - 1;
    }

    private int createNewConstant(MTType t) {
        return addSymbol(new Symbol("_k" + (constCtr++), t.toString(), 0, true, false));

    }

    private int createNewVar(MTType t) {
        return addSymbol(new Symbol("_v" + (varCtr++), t.toString(), 0, false, false));
    }

    // req: comb.len >= 2
    public int putCombination(int[] comb, MTType t) {
        int len = comb.length;
        int storeIdx = len - 2;
        boolean isVar = false;
        for (int i = 0; i < len; ++i) {
            comb[i] = getRootForNullary(comb[i]);
            if (!symbol_store.get(comb[i]).m_isConstant) isVar = true;
        }
        while (term_Store.size() <= storeIdx) {
            term_Store.add(new HashMap<int[], int[]>());
            rootMap.add(new HashMap<int[], Integer>());
        }
        if (!term_Store.get(storeIdx).containsKey(comb)) {
            term_Store.get(storeIdx).put(comb, comb);
            int rS = isVar ? createNewVar(t) : createNewConstant(t);
            rootMap.get(storeIdx).put(comb, rS);
            return rS;
        } else return rootMap.get(storeIdx).get(comb);

    }

    // req: s is a valid index
    public int getRootForNullary(int s) {
        int r = parray.get(s);
        if (s == r) return s;
        r = getRootForNullary(r);
        parray.set(s, r);
        return r;
    }

    // p is interpreted as the root of an expression tree.
    public int getSymbol(PSymbol p) {
        if (!stringTable.containsKey(p.getTopLevelOperation())) {
            stringTable.put(p.getTopLevelOperation(), symbol_store.size());
            parray.add(parray.size());
            symbol_store.add(new Symbol(p));
            assert parray.size() == symbol_store.size();
        }
        return getRootForNullary(stringTable.get(p.getTopLevelOperation().toString()));
    }

    public Symbol retrieveSymbol(int s){
        return symbol_store.get(parray.get(s));
    }
    public int merge(int i, int j) {
        i = getRootForNullary(i);
        j = getRootForNullary(j);
        Symbol is = symbol_store.get(i);
        Symbol js = symbol_store.get(j);
        int par = i;
        int chi = j;
        if (is.m_internal || (!is.m_isConstant && js.m_isConstant)) {
            par = j;
            chi = i;
        }
        parray.set(chi, par);
        if (toStringMap.containsKey(chi)) {
            toStringMap.put(par, toStringMap.get(chi));
        } else if (toStringMap.containsKey(par)) {
            toStringMap.put(chi, toStringMap.get(par));
        }
        return par;
    }

    public int getTerm(PSymbol p) {
        if (p.getSubExpressions().size() == 0) return getSymbol(p);
        /*if(p.getTopLevelOperation().equals("=")){
            return merge(getTerm((PSymbol)p.getSubExpressions().get(0)),
                    getTerm((PSymbol)p.getSubExpressions().get(1)));
        }*/
        int[] rAr = new int[p.getSubExpressions().size() + 1];
        rAr[0] = getSymbol(p);
        for (int i = 0; i < p.getSubExpressions().size(); ++i) {
            rAr[i+1] = getTerm((PSymbol) p.getSubExpressions().get(i));
        }
        int rS = putCombination(rAr, p.getType());
        toStringMap.put(rS, p);
        return rS;

    }

    public Clause introduceClause(Collection<PExp> clause) {
        Clause rClause = new Clause();
        for (PExp aDisj : clause) {
            int t;
            if (aDisj.getTopLevelOperation().equals("not")) {
                t = getTerm((PSymbol) aDisj.getSubExpressions().get(0));
                rClause.addPremise(t);
            } else {
                t = getTerm((PSymbol) aDisj);
                rClause.addConclusion(t);
            }
            if (!symbol_store.get(t).m_isConstant) {
                rClause.isGround = false;
            }
        }
        return rClause;
    }

    // return smallest string of elements of external symbols
    public String termString(int t) {
        int r = getRootForNullary(t);
        if (!symbol_store.get(r).m_internal)
            return symbol_store.get(r).m_name;

        return toStringMap.get(r).toString();


    }


}
