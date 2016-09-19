/**
 * FlatTermStore.java
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

import java.util.ArrayList;
import java.util.HashMap;

/**
 * Created by Mike on 9/9/2016.
 *
 * Assumptions: variables uniquely named.  No shared variables between clauses.
 * Symbols keyed on name.  Can't have a variable "S", as it could share same key as a program var.
 */
public class FlatTermStore {

    ArrayList<ArrayList<Integer>> term_Store;
    ArrayList<ArrayList<Integer>> free_Blocks;
    HashMap<String, Integer> stringTable;
    ArrayList<Symbol> symbol_store;

    public FlatTermStore(ClauseSet cs){
        term_Store = new ArrayList<>(4);
        term_Store.add(0,new ArrayList<Integer>(1024));

        stringTable = new HashMap<>(1024);

    }

    // ONly for symbols without arguments
    public int getSymbol(PSymbol p) {
        if (!stringTable.containsKey(p.toString())) {
            stringTable.put(p.toString(), symbol_store.size());
            symbol_store.add(new Symbol(p));
        }
        return stringTable.get(p.toString());
    }

    public int addPExp(PExp exp) {
        return 0;
    }

}
