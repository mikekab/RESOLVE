/**
 * CnfFlatClause.java
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

import java.util.HashMap;

/**
 * Created by Mike on 9/12/2016.
 */
public class CnfFlatClause {

    private HashMap<Integer, Integer> m_premises;
    private HashMap<Integer, Integer> m_conclusions;

    public CnfFlatClause(){
        m_premises = new HashMap<>();
        m_conclusions = new HashMap<>();
    }

    public void addPremise(int p) {
        int curCount = m_premises.containsKey(p) ? m_premises.get(p) : 0;
        m_premises.put(p, ++curCount);
    }

    public void addConclusion(int p) {
        int curCount = m_conclusions.containsKey(p) ? m_conclusions.get(p) : 0;
        m_conclusions.put(p, ++curCount);
    }
}
