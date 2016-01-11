/**
 * ConjunctionOfNormalizedAtomicExpressions.java
 * ---------------------------------
 * Copyright (c) 2015
 * RESOLVE Software Research Group
 * School of Computing
 * Clemson University
 * All rights reserved.
 * ---------------------------------
 * This file is subject to the terms and conditions defined in
 * file 'LICENSE.txt', which is part of this source code package.
 */
package edu.clemson.cs.r2jt.congruenceclassprover;

import edu.clemson.cs.r2jt.rewriteprover.*;
import edu.clemson.cs.r2jt.rewriteprover.absyn.*;
import edu.clemson.cs.r2jt.typeandpopulate.MTFunction;
import edu.clemson.cs.r2jt.typeandpopulate.MTType;
import edu.clemson.cs.r2jt.vcgeneration.vcs.VerificationCondition;

import java.lang.reflect.Array;
import java.util.*;

/**
 * Created by mike on 4/3/2014.
 */
public class ConjunctionOfNormalizedAtomicExpressions {

    private final Registry m_registry;
    protected final List<NormalizedAtomicExpressionMapImpl> m_exprList;
    protected long m_timeToEnd = -1;
    protected boolean m_evaluates_to_false = false;
    private int f_num = 0;
    private String m_current_justification = "";
    private final Map<Integer, Set<NormalizedAtomicExpressionMapImpl>> m_useMap;
    protected final VerificationConditionCongruenceClosureImpl m_VC;

    /**
     * @param registry the Registry symbols contained in the conjunction will
     *                 reference. This class will add entries to the registry if needed.
     */
    public ConjunctionOfNormalizedAtomicExpressions(Registry registry,
            VerificationConditionCongruenceClosureImpl vc) {
        m_registry = registry;
        // Array list is much slower than LinkedList for this application
        m_exprList = new LinkedList<NormalizedAtomicExpressionMapImpl>();
        m_useMap =
                new HashMap<Integer, Set<NormalizedAtomicExpressionMapImpl>>();
        m_VC = vc; // null if this is a theorem
    }

    protected int size() {
        return m_exprList.size();
    }

    protected void clear() {
        m_exprList.clear();
    }

    protected String addExpressionAndTrackChanges(PExp expression,
            long timeToEnd, String justification) {
        m_timeToEnd = timeToEnd;
        m_timeToEnd = Long.MAX_VALUE;
        m_current_justification = justification;
        String rString = "";
        rString += addExpression(expression);
        m_current_justification = "";
        updateUseMap();
        return rString;
    }

    // Top level
    protected String addExpression(PExp expression) {
        if (m_timeToEnd > 0 && System.currentTimeMillis() > m_timeToEnd) {
            return "";
        }
        String name = expression.getTopLevelOperation();
        if (expression.isEquality()) {
            int lhs = addFormula(expression.getSubExpressions().get(0));
            int rhs = addFormula(expression.getSubExpressions().get(1));
            return mergeOperators(lhs, rhs);
        }
        else if (name.equals("and")) {
            String r = "";
            r += addExpression(expression.getSubExpressions().get(0));
            r += addExpression(expression.getSubExpressions().get(1));
            return r;
        }
        else {
            MTType type = expression.getType();
            PSymbol asPsymbol = (PSymbol) expression;
            int intRepOfOp = addPsymbol(asPsymbol);
            int root = addFormula(expression);
            if (m_evaluates_to_false)
                return "";
            if (type.isBoolean()) {
                return mergeOperators(m_registry.getIndexForSymbol("true"),
                        root);
            }
        }
        return "";
    }


    // adds a particular symbol to the registry
    protected int addPsymbol(PSymbol ps) {
        String name = ps.getTopLevelOperation();
        MTType type = ps.getType();
        Registry.Usage usage = Registry.Usage.SINGULAR_VARIABLE;
        if (ps.isLiteral()) {
            usage = Registry.Usage.LITERAL;
        }
        else if (ps.isFunction()
                || ps.getType().getClass().getSimpleName().equals("MTFunction")) {
            if (ps.quantification.equals(PSymbol.Quantification.FOR_ALL)) {
                usage = Registry.Usage.HASARGS_FORALL;
            }
            else {
                usage = Registry.Usage.HASARGS_SINGULAR;
            }

        }
        else if (ps.quantification.equals(PSymbol.Quantification.FOR_ALL)) {
            usage = Registry.Usage.FORALL;
        }
        // The type stored with expressions is actually the range type
        // Ex: (S = T):B.
        // However, I need to store types for functions/relations.
        // Building these here.
        // It would be far better to handle this upstream.
        // Currently PExps from theorems have correct type set already
        if (ps.getSubExpressions().size() > 0) {
            List<MTType> paramList = new ArrayList<MTType>();
            for (PExp pParam : ps.getSubExpressions()) {
                paramList.add(pParam.getType());
            }
            type = new MTFunction(m_registry.m_typeGraph, type, paramList);
        }
        return m_registry.addSymbol(name, type, usage);
    }

    /* experimentally handling =
     i.e.: (|?S| = 0) = (?S = Empty_String))
     is broken down by addExpression so (|?S| = 0) is an argument
     should return int for true if known to be equal, otherwise return root representative. 
     */
    protected int addFormula(PExp formula) {
        if (formula.isEquality()) {
            int lhs = addFormula(formula.getSubExpressions().get(0));
            PExp r = formula.getSubExpressions().get(1);
            int rhs = addFormula(r);
            lhs = m_registry.findAndCompress(lhs);
            rhs = m_registry.findAndCompress(rhs);
            // This prevents matching of (i=i)=true, which is not built in
            /*if (lhs == rhs) {
                return m_registry.getIndexForSymbol("true");
            }
            else {*/
            // insert =(lhs,rhs) = someNewRoot
            int questEq = m_registry.getIndexForSymbol("=");
            NormalizedAtomicExpressionMapImpl pred =
                    new NormalizedAtomicExpressionMapImpl();
            pred.writeOnto(questEq, 0);
            pred.writeOnto(lhs, 1);
            pred.writeOnto(rhs, 2);
            return addAtomicFormula(pred);
            // }
        }
        PSymbol asPsymbol;
        if (!(formula instanceof PSymbol)) {
            System.err.println("unhandled PExp: " + formula.toString());
            throw new RuntimeException();

        }
        else
            asPsymbol = (PSymbol) formula;
        int intRepOfOp = addPsymbol(asPsymbol);
        // base case
        if (formula.isVariable()) {
            return intRepOfOp;
        }

        NormalizedAtomicExpressionMapImpl newExpr =
                new NormalizedAtomicExpressionMapImpl();
        newExpr.writeOnto(intRepOfOp, 0);
        int pos = 0;
        PExpSubexpressionIterator it = formula.getSubExpressionIterator();
        while (it.hasNext()) {
            PExp p = it.next();
            pos++;
            int root = addFormula(p);
            assert newExpr != null;
            newExpr.writeOnto(root, pos);
        }
        if (m_evaluates_to_false) {
            return -1;
        }
        Map<Integer, Integer> changedOps = new HashMap<Integer, Integer>();
        for (int k : newExpr.getKeys()) {
            int kPar = m_registry.findAndCompress(k);
            if (kPar != k) {
                changedOps.put(k, kPar);
            }
        }
        for (int k : changedOps.keySet()) {
            newExpr.replaceOperator(k, changedOps.get(k));
        }
        return addAtomicFormula(newExpr);
    }

    /**
     * @param atomicFormula one sided expression. (= new root) is appended and
     *                      expression is inserted if no match of the side is found. Otherwise
     *                      current root is returned.
     * @return current integer value of root symbol that represents the input.
     */
    private int addAtomicFormula(NormalizedAtomicExpressionMapImpl atomicFormula) {
        // Order terms if operator is commutative
        if (m_registry.isCommutative(atomicFormula.readPosition(0))) {
            atomicFormula = atomicFormula.withOrderedArguments();
        }
        int posIfFound = Collections.binarySearch(m_exprList, atomicFormula);
        if (posIfFound >= 0) {
            return m_exprList.get(posIfFound).readRoot();
        }
        // no such formula exists
        int indexToInsert = -(posIfFound + 1);
        MTType typeOfFormula =
                m_registry.getTypeByIndex(atomicFormula.readPosition(0));
        // this is the full type and is necessarily a function type

        MTType rangeType = ((MTFunction) typeOfFormula).getRange();
        String symName =
                m_registry.getSymbolForIndex(atomicFormula.readPosition(0));
        assert rangeType != null : symName + " has null type";
        // if any of the symbols in atomicFormula are variables (FORALL) make created symbol a variable
        boolean isVar = false;
        for (Integer is : atomicFormula.getKeys()) {
            String s = m_registry.getSymbolForIndex(is);
            if (s.startsWith("¢v")) {
                isVar = true;
                break;
            }
            Registry.Usage us = m_registry.getUsage(s);
            if (us == Registry.Usage.FORALL
                    || us == Registry.Usage.HASARGS_FORALL) {
                isVar = true;
                break;
            }
        }
        int rhs = m_registry.makeSymbol(rangeType, isVar);
        atomicFormula.writeToRoot(rhs);
        m_exprList.add(indexToInsert, atomicFormula);
        return rhs;
    }

    protected String mergeOperators(int a, int b) {
        int t = m_registry.getIndexForSymbol("true");
        int f = m_registry.getIndexForSymbol("false");

        String rString = "";
        if (m_timeToEnd > 0 && System.currentTimeMillis() > m_timeToEnd) {
            return rString;
        }
        a = m_registry.findAndCompress(a);
        b = m_registry.findAndCompress(b);
        if (a == b)
            return "";
        Stack<Integer> holdingTank = new Stack<Integer>();
        holdingTank.push(a);
        holdingTank.push(b);

        while (holdingTank != null && !holdingTank.empty()) {
            if (m_timeToEnd > 0 && System.currentTimeMillis() > m_timeToEnd) {
                return rString;
            }
            int opB = m_registry.findAndCompress(holdingTank.pop());
            int opA = m_registry.findAndCompress(holdingTank.pop());
            // Want to replace quantified vars with constant if it is equal to the constant
            int keeper = chooseSymbolToKeep(opA, opB);
            if (keeper == opB) {
                int temp = opA;
                opA = opB;
                opB = temp;
            }
            if ((opA == t && opB == f)) {
                m_evaluates_to_false = true;
                return "contradiction detected " + rString;
            }
            rString +=
                    m_registry.getSymbolForIndex(opA) + "/"
                            + m_registry.getSymbolForIndex(opB) + ",";
            Stack<Integer> mResult = mergeOnlyArgumentOperators(opA, opB);

            if (mResult != null)
                holdingTank.addAll(mResult);

        }
        return rString;
    }

    // need to choose literals over vars for theorem matching purposes
    // i.e. the theorem expression should keep the literals
    protected int chooseSymbolToKeep(int a, int b) {
        String s = m_registry.m_indexToSymbol.get(a);
        if (s.contains("¢")) {
            if (!m_registry.m_indexToSymbol.get(b).contains("¢"))
                return b; // a is created, b is not
            else
                return a < b ? a : b; // a is created, b is created
        }
        if (m_registry.getUsage(s).equals(Registry.Usage.FORALL))
            return b; // a is quantified
        return a < b ? a : b;
    }

    // Return list of modified predicates by their position. Only these can cause new merges.
    // b is replaced by a
    protected Stack<Integer> mergeOnlyArgumentOperators(int a, int b) {
        if (m_timeToEnd > 0 && System.currentTimeMillis() > m_timeToEnd) {
            return null;
        }
        if(a == b) return null;
        Iterator<NormalizedAtomicExpressionMapImpl> it = m_exprList.iterator();
        Stack<NormalizedAtomicExpressionMapImpl> modifiedEntries =
                new Stack<NormalizedAtomicExpressionMapImpl>();
        Stack<Integer> coincidentalMergeHoldingTank = new Stack<Integer>();
        while (it.hasNext()) {
            NormalizedAtomicExpressionMapImpl curr = it.next();
            if (curr.replaceOperator(b, a)) {
                if (m_registry.isCommutative(curr.readPosition(0))) {
                    curr = curr.withOrderedArguments();
                }
                modifiedEntries.push(curr);
                it.remove();
            }
        }
        while (!modifiedEntries.empty()) {
            int indexToInsert =
                    Collections
                            .binarySearch(m_exprList, modifiedEntries.peek());
            // If the modified one is already there, don't put it back
            if (indexToInsert < 0) {
                indexToInsert = -(indexToInsert + 1);
                NormalizedAtomicExpressionMapImpl nm = modifiedEntries.peek();

                    applyBuiltInLogicArity2(nm,coincidentalMergeHoldingTank);

                m_exprList.add(indexToInsert, modifiedEntries.pop());

            }
            else {
                // the expr is in the list, but are the roots different?
                int rootA = modifiedEntries.pop().readRoot();
                int rootB = m_exprList.get(indexToInsert).readRoot();
                if (rootA != rootB) {
                    coincidentalMergeHoldingTank.push(rootA);
                    coincidentalMergeHoldingTank.push(rootB);
                }
            }
        }

        m_registry.substitute(a, b);
        return coincidentalMergeHoldingTank;
    }
    private void applyBuiltInLogicArity2(NormalizedAtomicExpressionMapImpl nm, Stack<Integer> tank){
        if (nm.getArity()!=2) return;
        int op = nm.readPosition(0);
        int arg1 = nm.readPosition(1);
        int arg2 = nm.readPosition(2);
        int rhs = nm.readRoot();
        int tr = m_registry.getIndexForSymbol("true");
        int fl = m_registry.getIndexForSymbol("false");
        // =,true,false,not.  recorded first in reg. logic relation args (and, or, =) are ordered.
        // guard: return if all constant
        if((arg1 == tr || arg1 == fl)&&(arg2 == tr || arg2 == fl) && (rhs == tr || rhs == fl) ) return;
        // guard: return if all var
        //if((arg1 != tr && arg1 != fl)&&(arg2 != tr && arg2 != fl) && (rhs != tr && rhs != fl) ) return;
        // rules for and
        if(m_registry.m_symbolToIndex.containsKey("and") && op == m_registry.getIndexForSymbol("and")){
            // constant rhs
            if(rhs == tr){
                // (p and q) = t |= t/p, t/q
                if(tr!=arg1) {
                    tank.push(tr);
                    tank.push(arg1);
                }
                if(tr!=arg2) {
                    tank.push(tr);
                    tank.push(arg2);
                }
            }
            // constant t arg
            else if(arg1 == tr){
                // (t and p) = q |= p/q
                if(rhs!=arg2) {
                    tank.push(rhs);
                    tank.push(arg2);
                }
            }
            // constant f arg
            else if(arg1 == fl){
                // (f and p) = q |= f/q
                if(fl!=rhs) {
                    tank.push(fl);
                    tank.push(rhs);
                }
            }
            // all vars
            else if(arg1 == arg2){
                // (p = p) = q |= t/q
                if(tr!=rhs){
                    tank.push(tr);
                    tank.push(rhs);
                }
            }
        }
        else if(m_registry.m_symbolToIndex.containsKey("or") && op == m_registry.getIndexForSymbol("or")){
            // constant f rhs
            if(rhs == fl){
                // p or q = f |= f/p/q
                if(fl!=arg1) {
                    tank.push(fl);
                    tank.push(arg1);
                }
                if(fl!=arg2) {
                    tank.push(fl);
                    tank.push(arg2);
                }
            }
            // constant t arg
            else if(arg1 == tr){
                // (t or p) = q |= t/q
                if(tr!=rhs) {
                    tank.push(tr);
                    tank.push(rhs);
                }
            }
            // constant f arg
            else if(arg1 == fl){
                // (f or p) = q |= p/q
                if(arg2!=rhs) {
                    tank.push(arg2);
                    tank.push(rhs);
                }
            }
            // all vars.
            // p or not p = q := t/q
        }
        else if(op == m_registry.getIndexForSymbol("=")){
            // constant t rhs
            if(rhs == tr){
                // (p = q) = t |= p/q
                if(arg1!=arg2) {
                    tank.push(arg1);
                    tank.push(arg2);
                }
            }
            // constant f rhs
            else if(rhs == fl){
                // constant t arg
                if(arg1 == tr){
                    if(fl!=arg2) {
                        // (t = p) = f |= f/p
                        tank.push(fl);
                        tank.push(arg2);
                    }
                }
                // constant f arg
                if(arg1 == fl){
                    // (f = p) = f |= t/p
                    if(tr!=arg2) {
                        tank.push(tr);
                        tank.push(arg2);
                    }
                }
            }
            // constant t arg
            else if(arg1 == tr){
                // (t = p) = q |= p/q
                if(arg2!=rhs) {
                    tank.push(arg2);
                    tank.push(rhs);
                }
            }
        }


    }
    protected void updateUseMap() {
        m_useMap.clear();
        assert m_useMap.size() == 0;
        for (NormalizedAtomicExpressionMapImpl e : m_exprList) {
            for (Integer k : e.getKeys()) {
                assert m_registry.findAndCompress(k) == k : "child symbol in conj:"
                        + m_registry.getSymbolForIndex(k)
                        + " "
                        + k
                        + " "
                        + m_registry.m_indexToSymbol.get(k)
                        + " "
                        + e.toHumanReadableString(m_registry)
                        + " "
                        + e.toString();
                if (m_useMap.containsKey(k))
                    m_useMap.get(k).add(e);
                else {
                    HashSet<NormalizedAtomicExpressionMapImpl> nm =
                            new HashSet<NormalizedAtomicExpressionMapImpl>();
                    nm.add(e);
                    m_useMap.put(k, nm);
                }
            }
        }
        // for debug
        /*String s = "";
        for(Integer k : m_useMap.keySet()){
            s += m_registry.getSymbolForIndex(k) + "\n";
            for(NormalizedAtomicExpressionMapImpl nm : m_useMap.get(k)){
                s += nm.toHumanReadableString(m_registry) + "\n";
            }
            s += "\n";
        }
        System.err.println(s);*/
        for (Integer k : m_useMap.keySet()) {
            assert !m_useMap.get(k).isEmpty();
            assert m_useMap.get(k).size() != 0;
        }
    }

    protected Set<NormalizedAtomicExpressionMapImpl> multiKeyUseMapSearch(
            Set<String> keys) {

        Set<NormalizedAtomicExpressionMapImpl> resultSet =
                new HashSet<NormalizedAtomicExpressionMapImpl>();
        boolean firstkey = true;
        for (String k : keys) {
            int rKey = m_registry.getIndexForSymbol(k);
            if (!m_useMap.containsKey(rKey)) {
                return null;
            }
            Set<NormalizedAtomicExpressionMapImpl> tResults =
                    new HashSet<NormalizedAtomicExpressionMapImpl>(m_useMap
                            .get(rKey));
            if (tResults == null || tResults.isEmpty())
                return null;
            if (firstkey) {
                resultSet = tResults;
                firstkey = false;
            }
            else { // result is intersection
                resultSet.retainAll(tResults);
            }
        }
        return resultSet;
    }

    protected Set<java.util.Map<String, String>> getMatchesForOverideSet(
            NormalizedAtomicExpressionMapImpl expr, Registry exprReg,
            Set<Map<String, String>> foreignSymbolOverideSet) {
        Set<java.util.Map<String, String>> rSet =
                new HashSet<Map<String, String>>();
        for (Map<String, String> fs_m : foreignSymbolOverideSet) {
            Set<java.util.Map<String, String>> results =
                    getMatchesForEq(expr, exprReg, fs_m);
            if (results != null && results.size() != 0)
                rSet.addAll(results);
        }
        return rSet;
    }

    protected Set<Map<String, String>> getMatchesForEq(
            NormalizedAtomicExpressionMapImpl expr, Registry exprReg,
            Map<String, String> foreignSymbolOveride) {
        // Identify the literals.
        Set<String> literalsInexpr = new HashSet<String>();
        Map<String, Integer> exprMMap =
                expr.getEquationOperatorsAsStrings(exprReg);
        for (String s : exprMMap.keySet()) {
            String lit = "";
            if (!foreignSymbolOveride.containsKey(s)) {
                lit = s;
            }
            else if (!foreignSymbolOveride.get(s).equals("")) {
                // wildcard may have been bound in search for another expression
                lit = foreignSymbolOveride.get(s);
            }
            if (!lit.equals("")) {
                if (!m_registry.m_symbolToIndex.containsKey(lit))
                    return null;
                literalsInexpr.add(lit);
            }

        }

        Set<NormalizedAtomicExpressionMapImpl> vCNaemlsWithAllLiterals =
                multiKeyUseMapSearch(literalsInexpr);
        if (vCNaemlsWithAllLiterals == null)
            return null;

        Set<NormalizedAtomicExpressionMapImpl> filtered_vcNaemlsWithAllLiterals;
        // std filter. opnum -> bitcode. means opnum must be used at each position indicated by the bitcode
        NormalizedAtomicExpressionMapImpl filter =
                new NormalizedAtomicExpressionMapImpl();
        for (String s : literalsInexpr) {
            // all literals in the search expr have to already be in the Vc.
            // find all positions
            int allPositionsLitIsUsedInSearchExpr = 0;
            int vcInt = m_registry.getIndexForSymbol(s);
            assert vcInt >= 0 : s + " not in VC registry";
            // Have to handle case where the literal is part of the the theorem,
            // AND a wildcard has been bound to the same symbol
            if (exprReg.m_symbolToIndex.containsKey(s)) {
                int sInt = exprReg.getIndexForSymbol(s);
                allPositionsLitIsUsedInSearchExpr = expr.readOperator(sInt);
            }

            for (String baseMapK : foreignSymbolOveride.keySet()) {
                if (foreignSymbolOveride.get(baseMapK).equals(s)) {
                    allPositionsLitIsUsedInSearchExpr |=
                            expr.readOperator(exprReg
                                    .getIndexForSymbol(baseMapK));
                }
            }
            filter.overwriteEntry(vcInt, allPositionsLitIsUsedInSearchExpr);

        }

        boolean isCommutOp = exprReg.isCommutative(expr.readPosition(0));

        if (!isCommutOp) {
            filtered_vcNaemlsWithAllLiterals =
                    nonCommutativeFilter(vCNaemlsWithAllLiterals, filter);
            if (filtered_vcNaemlsWithAllLiterals.isEmpty())
                return null;
            return getBindings_NonCommutative(filtered_vcNaemlsWithAllLiterals,
                    foreignSymbolOveride, expr, exprReg);
        }
        else {
            filtered_vcNaemlsWithAllLiterals =
                    commutativeFilter(vCNaemlsWithAllLiterals, filter);
            if (filtered_vcNaemlsWithAllLiterals.isEmpty())
                return null;
            return getBindings_Commutative(filtered_vcNaemlsWithAllLiterals,
                    foreignSymbolOveride, expr, exprReg);
        }
    }

    // Should be able to assume literals in root/pos 0 match (else the filter didnt work)
    // And lits that are args are at least used as many times as in the theorem
    Set<Map<String, String>> getBindings_Commutative(
            Set<NormalizedAtomicExpressionMapImpl> vcEquations,
            Map<String, String> basemap,
            NormalizedAtomicExpressionMapImpl searchExpr, Registry searchReg) {
        // Argument sets
        Map<String, Integer> thArgs =
                searchExpr.getArgumentsAsStrings(searchReg);
        Map<String, Integer> thOps =
                searchExpr.getEquationOperatorsAsStrings(searchReg);
        Deque<String> thOpsLitFirst = new LinkedList<String>();
        for (String thOp : thOps.keySet()) {
            if (!basemap.containsKey(thOp) || !basemap.get(thOp).equals("")) {
                thOpsLitFirst.addFirst(thOp);
            }
            else {
                thOpsLitFirst.addLast(thOp);
            }
        }
        Set<Map<String, String>> bindings = new HashSet<Map<String, String>>();
        bindToAVCEquation: for (NormalizedAtomicExpressionMapImpl vc_r : vcEquations) {
            Map<String, String> currentBind =
                    new HashMap<String, String>(basemap);
            Map<String, Integer> vcArgs =
                    vc_r.getArgumentsAsStrings(m_registry);
            Stack<String> comVCargsBound = new Stack<String>();
            ArrayList<String> comTargsBound = new ArrayList<String>();
            for (String thOp : thOpsLitFirst) {
                if (!basemap.containsKey(thOp) || !basemap.get(thOp).equals("")) {
                    // This is a literal
                    // Remove num uses as arg from arg count
                    if (basemap.containsKey(thOp) && thArgs.containsKey(thOp)) {
                        // Wildcard argument has already been bound
                        int numUses = thArgs.get(thOp);
                        String lit =
                                m_registry.getRootSymbolForSymbol(basemap
                                        .get(thOp));
                        // May be in commutative section
                        if (vcArgs.containsKey(lit)) {
                            vcArgs.put(lit, vcArgs.get(lit) - numUses);
                        }
                        else { // lit is arg of theorem, but not arg of vcEq
                            continue bindToAVCEquation; // shoulndt happen
                        }
                    }
                    else if (thArgs.containsKey(thOp)) {
                        // arg literal that exists in both places, not ever was wildcard
                        int numUses = thArgs.get(thOp);
                        thOp = m_registry.getRootSymbolForSymbol(thOp);
                        if (vcArgs.containsKey(thOp)) {
                            vcArgs.put(thOp, vcArgs.get(thOp) - numUses);
                        }
                        else {
                            continue bindToAVCEquation; // shouldnt happen
                        }
                    }
                    continue; // go to next op
                }
                // thOp must be a wildcard
                String wild = thOp;
                int wildOpCode = searchReg.getIndexForSymbol(wild);
                int wildPosBitCode = searchExpr.readOperator(wildOpCode);
                // Basemap is used over a set of equations; ie wild may not even be used in this one
                if (wildPosBitCode <= 0)
                    continue;
                String localToBindTo = "";

                boolean isRoot = searchExpr.readRoot() == wildOpCode;
                boolean isFSymb = searchExpr.readPosition(0) == wildOpCode;
                boolean isArgOnly = false;
                if (isRoot || isFSymb) {
                    isArgOnly = false;
                    if ((wildPosBitCode & (wildPosBitCode - 1)) == 0) { // Single use and is func symbol or root
                        localToBindTo =
                                m_registry.getSymbolForIndex(vc_r
                                        .readPositionBitcode(wildPosBitCode));
                    }
                    else {// used as (root or func symb) and as arg(s) in search
                        // so reject if same not true of vcr
                        String loc = "";
                        if (isRoot && isFSymb) {
                            if (vc_r.readPosition(0) == vc_r.readRoot()) {
                                loc =
                                        m_registry.getSymbolForIndex(vc_r
                                                .readRoot());
                            }
                        }
                        else if (isFSymb) {
                            loc =
                                    m_registry.getSymbolForIndex(vc_r
                                            .readPosition(0));
                        }
                        else if (isRoot) {
                            loc = m_registry.getSymbolForIndex(vc_r.readRoot());
                        }
                        if (!loc.equals("")) {
                            int thC = thArgs.get(wild);
                            int vcC = vcArgs.get(loc);
                            if (thC <= vcC) {
                                vcArgs.put(loc, vcC - thC);
                                localToBindTo = loc;
                            }
                            else
                                continue bindToAVCEquation;
                        }
                        else
                            continue bindToAVCEquation;
                    }
                }
                // Only use is in arg list
                else {
                    isArgOnly = true;
                    int thC = thArgs.get(wild);
                    // Choose the first that has the min no. of uses.  (Going to potentially miss some matches)
                    for (String vcA : vcArgs.keySet()) {
                        int vcACnt = vcArgs.get(vcA);
                        if (thC <= vcACnt) {
                            localToBindTo = vcA;
                            vcArgs.put(localToBindTo, vcACnt - thC);
                            break;
                        }
                    }
                }
                if (!localToBindTo.equals("")) {
                    MTType wildType =
                            searchReg.getTypeByIndex(searchReg
                                    .getIndexForSymbol(wild));
                    MTType localType =
                            m_registry.getTypeByIndex(m_registry
                                    .getIndexForSymbol(localToBindTo));
                    if (!m_registry.isSubtype(localType, wildType))
                        continue bindToAVCEquation;
                    currentBind.put(wild, localToBindTo);
                    if (isArgOnly) {
                        comTargsBound.add(wild);
                        comVCargsBound.push(localToBindTo);
                    }
                }
                else
                    continue bindToAVCEquation;

            }
            bindings.add(currentBind);
            Map<String, String> rotBind =
                    new HashMap<String, String>(currentBind);
            // do simple rotation permutations
            for (String tArg : comTargsBound) {
                String locSym = comVCargsBound.pop();
                MTType wildType =
                        searchReg.getTypeByIndex(searchReg
                                .getIndexForSymbol(tArg));
                MTType locType =
                        m_registry.getTypeByIndex(m_registry
                                .getIndexForSymbol(locSym));
                if (m_registry.isSubtype(locType, wildType))
                    rotBind.put(tArg, locSym);
            }
            if (!rotBind.isEmpty())
                bindings.add(rotBind);
        }
        // Have to typecheck again.  Might have 1 nat, 1 Z arg of + for ex.
        // Just rotating.  Complete for 2 args bound, which is good enough for now.

        return bindings;
    }

    // Most self time in this entire package
    Set<Map<String, String>> getBindings_NonCommutative(
            Set<NormalizedAtomicExpressionMapImpl> vcEquations,
            Map<String, String> basemap,
            NormalizedAtomicExpressionMapImpl searchExpr, Registry searchReg) {
        Set<Map<String, String>> bindings = new HashSet<Map<String, String>>();
        bindToAVCEquation: for (NormalizedAtomicExpressionMapImpl vc_r : vcEquations) {
            Map<String, String> currentBind =
                    new HashMap<String, String>(basemap);
            for (String wild : basemap.keySet()) {
                String wildVal = basemap.get(wild);
                if (wildVal.equals("")) {
                    int wildInt = searchReg.getIndexForSymbol(wild);
                    int wildP_BitCode = searchExpr.readOperator(wildInt);
                    if (wildP_BitCode <= 0)
                        continue; // wild not used in this eq.
                    int vc_eq_op = vc_r.readPositionBitcode(wildP_BitCode);
                    if (vc_eq_op == -1)
                        continue bindToAVCEquation; // non matching due to wildcard symbol used more places than found
                    String localToBindTo =
                            m_registry.getSymbolForIndex(vc_eq_op);
                    MTType wildType =
                            searchReg.getTypeByIndex(searchReg
                                    .getIndexForSymbol(wild));
                    MTType localType =
                            m_registry.getTypeByIndex(m_registry
                                    .getIndexForSymbol(localToBindTo));
                    if (!m_registry.isSubtype(localType, wildType))//10_4 of Queue_Examples_Fac: 2.7 secs
                        //if(!localType.isSubtypeOf(wildType)) // 10_4 of Queue_Examples_Fac: 4.8 secs
                        continue bindToAVCEquation;
                    currentBind.put(wild, localToBindTo);
                }
            }
            bindings.add(currentBind);
        }
        return bindings;
    }

    protected Set<NormalizedAtomicExpressionMapImpl> commutativeFilter(
            Set<NormalizedAtomicExpressionMapImpl> raw,
            NormalizedAtomicExpressionMapImpl filter_criteria) {
        Set<NormalizedAtomicExpressionMapImpl> filteredSet =
                new HashSet<NormalizedAtomicExpressionMapImpl>();
        Map<String, Integer> filterLitArgs =
                filter_criteria.getArgumentsAsStrings(m_registry);
        nextExpr: for (NormalizedAtomicExpressionMapImpl r_n : raw) {
            if ((filter_criteria.readPosition(0) != -1 && filter_criteria
                    .readPosition(0) != r_n.readPosition(0))
                    || (filter_criteria.readRoot() != -1 && filter_criteria
                            .readRoot() != r_n.readRoot()))
                continue nextExpr;
            Map<String, Integer> r_n_litArgs =
                    r_n.getArgumentsAsStrings(m_registry);
            for (String arg : filterLitArgs.keySet()) {
                if (!r_n_litArgs.containsKey(arg))
                    continue nextExpr;
                if (filterLitArgs.get(arg) > r_n_litArgs.get(arg))
                    continue nextExpr;
            }
            filteredSet.add(r_n);
        }
        return filteredSet;
    }

    protected Set<NormalizedAtomicExpressionMapImpl> nonCommutativeFilter(
            Set<NormalizedAtomicExpressionMapImpl> raw,
            NormalizedAtomicExpressionMapImpl filter_criteria) {
        Set<NormalizedAtomicExpressionMapImpl> filteredSet =
                new HashSet<NormalizedAtomicExpressionMapImpl>();
        for (NormalizedAtomicExpressionMapImpl r_n : raw) {
            // r_n & filter_criteria ex. 1111 & 1001
            boolean matches = true;
            for (int litOp : filter_criteria.getKeys()) {
                int vcBitCodeForLitOp = r_n.readOperator(litOp);
                int filterBitCodeForLitOp = filter_criteria.readOperator(litOp);
                if ((vcBitCodeForLitOp & filterBitCodeForLitOp) != filterBitCodeForLitOp) {
                    matches = false;
                    break;
                }
            }
            if (matches)
                filteredSet.add(r_n);
        }
        return filteredSet;
    }

    protected Map<String, Integer> getSymbolProximity(Set<String> symbols) {
        boolean done = false;
        Map<Integer, Integer> relatedKeys = new HashMap<Integer, Integer>();
        for (String s : symbols) {
            relatedKeys.put(m_registry.getIndexForSymbol(s), 0);
        }
        int closeness = 0;
        Set<Integer> relatedSet = new HashSet<Integer>();

        while (!done) {
            closeness++;
            int startSize = relatedKeys.size();
            HashMap<Integer, Integer> relatedKeys2 =
                    new HashMap<Integer, Integer>();
            for (int i = 0; i < m_exprList.size(); ++i) {
                if (relatedSet.contains(i))
                    continue;
                Set<Integer> intersection =
                        new HashSet<Integer>(m_exprList.get(i).getKeys());
                intersection.retainAll(relatedKeys.keySet());
                if (!intersection.isEmpty()) {
                    relatedSet.add(i);
                    for (Integer k : m_exprList.get(i).getKeys()) {
                        if (!relatedKeys.containsKey(k)) {
                            relatedKeys2.put(k, closeness);
                        }
                    }
                }
            }
            relatedKeys.putAll(relatedKeys2);
            if (startSize == relatedKeys.size()) {
                done = true;
            }
        }

        Map<String, Integer> rMap =
                new HashMap<String, Integer>(relatedKeys.size());
        for (Integer i : relatedKeys.keySet()) {
            rMap.put(m_registry.getSymbolForIndex(i), relatedKeys.get(i));
        }
        rMap.put("_most_distant", closeness); // for scaling
        return rMap;
    }

    @Override
    public String toString() {
        String r = "";
        if (m_evaluates_to_false)
            r += "Conjunction evaluates to false" + "\n";
        /*        for (MTType key : m_registry.m_typeToSetOfOperators.keySet()) {
         r += key.toString() + ":\n";
         r += m_registry.m_typeToSetOfOperators.get(key) + "\n\n";
         }
         */
        for (NormalizedAtomicExpressionMapImpl cur : m_exprList) {
            r += cur.toHumanReadableString(m_registry) + "\n";
        }
        return r;
    }

}
