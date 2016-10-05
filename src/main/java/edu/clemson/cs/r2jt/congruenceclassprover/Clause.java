package edu.clemson.cs.r2jt.congruenceclassprover;

import java.util.*;

/**
 * Created by Mike on 9/21/2016.
 */
public class Clause {

    public Set<Integer> disjuncts;

    boolean isTaut = false;
    public boolean isGround = true;
    public Clause(){
        disjuncts = new HashSet<>();
    }
    // returns true if disjunct added, false if complement found.
    public boolean addPremise(int c){
        if(!disjuncts.contains(c)){
            disjuncts.add(-c);
            return true;
        }
        isTaut = true;
        return false;
    }
    public boolean addConclusion(int c){
        if(!disjuncts.contains(-c)){
            disjuncts.add(c);
            return true;
        }
        isTaut = true;
        return false;
    }
    public boolean equals(Object o){
        return (disjuncts.equals(o));
    }
    public int hashCode(){
        return disjuncts.hashCode();
    }
}
