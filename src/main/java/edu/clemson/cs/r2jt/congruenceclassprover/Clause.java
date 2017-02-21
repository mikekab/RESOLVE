/**
 * Clause.java
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
 * Created by Mike on 9/21/2016.
 */
public class Clause {

    protected SortedSet<Integer> disjuncts;

    boolean isTaut = false;
    public boolean isGround = true;

    public boolean isUnit() {
        return disjuncts.size() == 1;
    }

    public Clause(){
        disjuncts = new TreeSet<>();
    }

    public Clause(SortedSet<Integer> dSet, TermStore ts){
        disjuncts = new TreeSet<>();
        for(int d: dSet){
            addDisjunct(d,ts.retrieveSymbol(abs(d)).m_isConstant);
        }
    }

    // returns true if disjunct added, false if complement found.
    public int size() {
        return disjuncts.size();
    }

    public int numPositions(TermStore ts) {
        int sum = 0;
        for (int d : disjuncts) {
            sum += ts.termSize(abs(d));
        }
        return sum;
    }

    private int abs(int x) {
        if (x < 0)
            return -x;
        return x;
    }

    public Iterator<Integer> getDisjIterator() {
        return disjuncts.iterator();
    }

    public int symbolSum(){
        int r = 0;
        for(int i: disjuncts){
            r += abs(i);
        }
        return r;
    }

    public boolean containsAll(Clause o) {
        return disjuncts.containsAll(o.disjuncts);
    }

    public boolean addDisjunct(int d, boolean ground) {
        if (d < 0)
            return addPremise(-d, ground);
        return addConclusion(d, ground);
    }

    public boolean addPremise(int c, boolean ground) {
        if (c == 1)
            return false;
        if (c == 2) {
            disjuncts.clear();
            disjuncts.add(1);
            isTaut = true;
            return false;
        }
        if (!ground)
            isGround = false;
        if (!disjuncts.contains(c)) {
            disjuncts.add(-c);
            return true;
        }
        disjuncts.clear();
        disjuncts.add(1);
        isTaut = true;
        return false;
    }

    public SortedSet<Integer> lessADisj(int d){
        SortedSet<Integer> r = new TreeSet<>();
        r.addAll(disjuncts);
        r.remove(d);
        return r;
    }

    public boolean addConclusion(int c, boolean ground) {
        if (c == 2)
            return false;
        if (c == 1) {
            disjuncts.clear();
            disjuncts.add(1);
            isTaut = true;
            return false;
        }
        if (!ground)
            isGround = false;
        if (!disjuncts.contains(-c)) {
            disjuncts.add(c);
            return true;
        }

        disjuncts.clear();
        disjuncts.add(1);
        isTaut = true;
        return false;
    }

    public Clause updatedClause(TermStore ts) {
        Clause rC = new Clause();
        for (int d : disjuncts) {
            int absD = d < 0 ? -d : d;
            absD = ts.getRootForNullary(absD);
            if (d < 0) {
                rC.addPremise(absD, ts.retrieveSymbol(absD).m_isConstant);
            }
            else
                rC.addConclusion(absD, ts.retrieveSymbol(absD).m_isConstant);
        }
        if (rC.isUnit() && rC.disjuncts.first() == 1) {
            rC.isTaut = true;
        }
        return rC;
    }

    public boolean equals(Object o) {
        /*        if(!(o instanceof Clause))
         return false;
         if(o == this)
         return true;
         Clause c = (Clause)o;
         if(disjuncts.size()!= c.disjuncts.size())
         return false;
         Iterator<Integer> it = disjuncts.iterator();
         Iterator<Integer> cit = c.disjuncts.iterator();
         while(it.hasNext()){
         if(it.next()!=cit.next()) return false;
         }
         return true;
         */
        return disjuncts.equals(o);
    }

    public int hashCode() {
        return disjuncts.hashCode();
    }
}
