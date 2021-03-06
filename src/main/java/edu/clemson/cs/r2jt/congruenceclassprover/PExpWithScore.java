/**
 * PExpWithScore.java
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
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import edu.clemson.cs.r2jt.rewriteprover.absyn.*;

public class PExpWithScore implements Comparable<PExpWithScore> {

    protected PExp m_theorem;
    protected String m_theoremDefinitionString;
    protected Integer m_score = 1;
    protected Set<String> m_theorem_symbols;
    protected Map<String, String> m_bMap;

    public PExpWithScore(PExp theorem, Map<String, String> bMap,
            String justification) {
        m_theorem = theorem;
        m_theoremDefinitionString = justification;
        m_theorem_symbols = m_theorem.getSymbolNames();
        m_bMap = bMap;
    }

    @Override
    public String toString() {
        return m_theoremDefinitionString + "\n" + "\t[" + m_score + "]" + " "
                + m_theorem.toString() + "\t" + m_bMap + "\n";
    }

    @Override
    public int compareTo(PExpWithScore o) {
        return m_score - o.m_score;
    }
}