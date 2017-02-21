/**
 * ClauseSet.java
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

import edu.clemson.cs.r2jt.rewriteprover.*;
import edu.clemson.cs.r2jt.rewriteprover.absyn.PExp;
import edu.clemson.cs.r2jt.rewriteprover.absyn.PSymbol;
import edu.clemson.cs.r2jt.typeandpopulate.MTType;
import edu.clemson.cs.r2jt.typereasoning.TypeGraph;

import java.util.*;

/**
 * Created by Mike on 9/12/2016.
 */
public class ClauseSet {

    NavigableSet<Clause> clauseSet;
    NavigableSet<Clause> resolvedClauseSet;
    List<Clause> workedOff;
    Map<Integer, Set<Integer>> woDisjToWoClauseIndex;
    TypeGraph g;
    List<PExp> cnfExpTreeFmt;
    Map<String, Map<String, PExp>> cnfSetSets;
    PExp t;
    PExp f;
    MTType z;
    MTType n;
    TermStore termStore;
    int clauseCntr = 0;
    String tag;
    String log;
    String nl = "\n";
    String cycleLog = "";
    Set<String> woContainmentStringSet;
    Set<Clause> trueUnitClauseSingSet;
    Set<Integer> eqRoots;
    public int numUniqueResolventsFound = 0;

    private class ClauseComp implements Comparator<Clause> {

        public int compare(Clause a, Clause b) {
            //int symSumDiff = a.symbolSum() - b.symbolSum();
            //if(symSumDiff!=0) return symSumDiff;
            int diffPos = a.numPositions(termStore) - b.numPositions(termStore);
            if (diffPos != 0)
                return diffPos;
            int diff = a.size() - b.size();
            if (diff != 0)
                return diff;
            if (a.isGround != b.isGround) {
                if (a.isGround && !b.isGround)
                    return -1;
                else
                    return 1;
            }
            Iterator<Integer> aIt = a.getDisjIterator();
            Iterator<Integer> bIt = b.getDisjIterator();
            while (aIt.hasNext()) {
                Integer aI = aIt.next();
                Integer bI = bIt.next();
                if (!aI.equals(bI)) {
                    return aI - bI;
                }
            }
            return 0;

        }
    }

    public ClauseSet(TypeGraph graph, MTType Z, MTType N, String id) {
        g = graph;
        z = Z;
        n = N;
        tag = id;
        log = tag + "\n";

        clauseSet = new TreeSet<>(new ClauseComp());
        resolvedClauseSet = new TreeSet<>(new ClauseComp());
        cnfExpTreeFmt = new ArrayList<>();
        t = new PSymbol(g.BOOLEAN, null, "true");
        f = new PSymbol(g.BOOLEAN, null, "false");
        cnfSetSets = new HashMap<>();
        termStore = new TermStore();
        workedOff = termStore.workedOff;
        woDisjToWoClauseIndex = termStore.woDisjToWoClauseIndex;
        woContainmentStringSet = new HashSet<>(1024);
        Clause trueUnitClause = new Clause();
        trueUnitClause.addConclusion(1, true);
        trueUnitClauseSingSet = new HashSet<>();
        trueUnitClauseSingSet.add(trueUnitClause);
        eqRoots = new TreeSet<>();
    }

    public ClauseSet deepCopy() {
        ClauseSet cop = new ClauseSet(g, z, n, tag);

        return cop;
    }

    private void addTreeFmtToSetofSets(PExp p, TreeMap<String, PExp> clauseElem) {
        String top = p.getTopLevelOperation();
        switch (top) {
            case "and":
                addTreeFmtToSetofSets(p.getSubExpressions().get(0), clauseElem);
                addTreeFmtToSetofSets(p.getSubExpressions().get(1), new TreeMap<String, PExp>());
                break;
            case "or":
                splitOrs(p, clauseElem);
                // Remove any disj that is a variable not used anywhere else
                // Example, remove p,q from f(x, y), f(y, x), not(Is_Total(f)), p, q
                TreeMap<String, PExp> copy = new TreeMap<>();
                Iterator<Map.Entry<String, PExp>> it = clauseElem.entrySet().iterator();
                while (it.hasNext()) {
                    Map.Entry<String, PExp> n = it.next();
                    PSymbol ps = (PSymbol) n.getValue();
                    if (ps.getTopLevelOperation().equals("not")) {
                        ps = (PSymbol) ps.getSubExpressions().get(0);
                    }
                    if (!ps.quantification.equals(PSymbol.Quantification.FOR_ALL)) {
                        copy.put(n.getKey(), n.getValue());
                        it.remove();
                    }
                }
                it = clauseElem.entrySet().iterator();
                while (it.hasNext()) {
                    Map.Entry<String, PExp> n = it.next();
                    boolean isused = false;
                    for (Map.Entry<String, PExp> c : copy.entrySet()) {
                        if (c.getValue().getSymbolNames().contains(n.getKey())) {
                            isused = true;
                        }
                    }
                    if (!isused) {
                        it.remove();
                    }
                }
                copy.putAll(clauseElem);
                clauseElem = copy;

                if (!clauseElem.containsKey("true")) {
                    clauseElem = renameVarsInClause(clauseElem, ++clauseCntr);
                    cnfSetSets.put(clauseElem.keySet().toString(), clauseElem);
                }
                break;
            default:
                if (!clauseElem.containsKey("true")) {
                    clauseElem.put(p.toString(), p);
                    clauseElem = renameVarsInClause(clauseElem, ++clauseCntr);
                    cnfSetSets.put(clauseElem.keySet().toString(), clauseElem);
                }

        }

    }

    private TreeMap<String, PExp> renameVarsInClause(TreeMap<String, PExp> clause, int clauseCnt) {
        HashMap<String, Integer> ctrs = new HashMap<>();
        Set<PSymbol> clauseVars = new HashSet<>();
        for (Map.Entry<String, PExp> disj : clause.entrySet()) {
            clauseVars.addAll(disj.getValue().getQuantifiedVariables());
        }
        Map<PExp, PExp> replMap = new HashMap<>();
        for (PSymbol p : clauseVars) {
            String name = p.getType().toString();
            if (!ctrs.containsKey(name)) {
                ctrs.put(name, 0);
            }
            int curCount = ctrs.get(name) + 1;
            ctrs.put(name, curCount);
            //name = "_" + name + "." + curCount + "." + clauseCnt;
            name = "_" + name + "." + curCount;
            replMap.put(p, new PSymbol(p.getType(), p.getTypeValue(), name, p.quantification));
        }
        if (!replMap.isEmpty()) {
            TreeMap<String, PExp> replClause = new TreeMap<>();
            for (Map.Entry<String, PExp> disj : clause.entrySet()) {
                PExp r = disj.getValue().substitute(replMap);
                replClause.put(r.toString(), r);
            }
            clause = replClause;
        }
        return clause;
    }

    // remove or, return map of literals.
    // Ex: a or (b or (c or d)) returns collection a,b,c,d
    private void splitOrs(PExp p, TreeMap<String, PExp> col) {
        String top = p.getTopLevelOperation();
        if (top.equals("or")) {
            splitOrs(p.getSubExpressions().get(0), col);
            splitOrs(p.getSubExpressions().get(1), col);
        } else if (!col.containsKey("true")) {
            if (col.containsKey(("not(" + p.toString() + ")"))
                    || (top.equals("not") && col.containsKey(p
                    .getSubExpressions().get(0).toString()))) {
                col.clear();
                col.put("true", t);
            } else {
                col.put(p.toString(), p);
            }

        }
    }

    public void addVC(VC vc) {
        for (PExp p : vc.getConsequent().getMutableCopy()) {
            addClause(negate(p));
        }
        for (PExp p : vc.getAntecedent().getMutableCopy()) {
            addClause(p);
        }
    }

    public void initializeTermStore() {
        for (Map cMap : cnfSetSets.values()) {
            Clause c = termStore.introduceClause(cMap.values());
            if (!c.isTaut) {
                Set<Clause> subsumed = new HashSet<>();
                for (Clause cl : clauseSet) {
                    if (cl.containsAll(c)) {
                        subsumed.add(cl);
                    }
                }
                clauseSet.removeAll(subsumed);
                clauseSet.add(c);
            }
        }

    }

    public void addClause(PExp p) {
        p = Utilities.replacePExp(p, g, z, n);
        p = multipassSimpApplier(p);
        p = multipassNNFApplier(p);
        p = multipassCNFApplier(p);
        cnfExpTreeFmt.add(p);
        addTreeFmtToSetofSets(p, new TreeMap<String, PExp>());

    }

    private PExp multipassSimpApplier(PExp p) {
        String pS = "";
        while (!(pS.equals(p.toString()))) {
            pS = p.toString();
            p = depthFirstRecursiveSimpRuleApplier(p);
        }
        return p;
    }

    private PExp multipassNNFApplier(PExp p) {
        String pS = "";
        while (!(pS.equals(p.toString()))) {
            pS = p.toString();
            p = depthFirstRecursiveNNFRuleApplier(p, 1);
        }
        return p;
    }

    private PExp multipassCNFApplier(PExp p) {
        String pS = "";
        while (!(pS.equals(p.toString()))) {
            pS = p.toString();
            p = depthFirstRecursiveCNFRuleApplier(p);
        }
        return p;
    }

    private PExp depthFirstRecursiveSimpRuleApplier(PExp p) {
        ArrayList<PExp> argsA = new ArrayList<>();
        for (PExp arg : p.getSubExpressions()) {
            argsA.add(depthFirstRecursiveSimpRuleApplier(arg));
        }
        if (argsA.isEmpty())
            return p;
        ArrayList<PExp> argsB = new ArrayList<>();
        for (PExp pa : argsA) {
            argsB.add(applySimplificationRules(pa));
        }
        return applySimplificationRules(
                new PSymbol(p.getType(), p.getTypeValue(),
                        p.getTopLevelOperation(), argsB, ((PSymbol) p).quantification));
    }

    private PExp depthFirstRecursiveNNFRuleApplier(PExp p, int polarity) {
        ArrayList<PExp> argsA = new ArrayList<>();
        for (PExp arg : p.getSubExpressions()) {
            argsA.add(depthFirstRecursiveNNFRuleApplier(arg, polarity));
        }
        if (argsA.isEmpty())
            return p;
        ArrayList<PExp> argsB = new ArrayList<>();
        int polT = p.getTopLevelOperation().equals("not") ? -1 : polarity;
        for (PExp pa : argsA) {
            argsB.add(applyNNFRules(pa, polT));
        }
        return applyNNFRules(
                new PSymbol(p.getType(), p.getTypeValue(),
                        p.getTopLevelOperation(), argsB, ((PSymbol) p).quantification), polarity);
    }

    private PExp depthFirstRecursiveCNFRuleApplier(PExp p) {
        ArrayList<PExp> argsA = new ArrayList<>();
        for (PExp arg : p.getSubExpressions()) {
            argsA.add(depthFirstRecursiveCNFRuleApplier(arg));
        }
        if (argsA.isEmpty())
            return p;
        ArrayList<PExp> argsB = new ArrayList<>();
        for (PExp pa : argsA) {
            argsB.add(applyCNFRules(pa));
        }
        return applyCNFRules(
                new PSymbol(p.getType(), p.getTypeValue(),
                        p.getTopLevelOperation(), argsB, ((PSymbol) p).quantification));
    }

    private PExp applyCNFRules(PExp p) {
        if (!p.getTopLevelOperation().equals("or"))
            return p;
        PExp arg0 = p.getSubExpressions().get(0);
        PExp arg1 = p.getSubExpressions().get(1);
        if (arg0.getTopLevelOperation().equals("and")) {
            PExp arg0_0 = arg0.getSubExpressions().get(0);
            PExp arg0_1 = arg0.getSubExpressions().get(1);
            return conjunct(disjunct(arg1, arg0_0), disjunct(arg1, arg0_1));
        }
        if (arg1.getTopLevelOperation().equals("and")) {
            PExp arg1_0 = arg1.getSubExpressions().get(0);
            PExp arg1_1 = arg1.getSubExpressions().get(1);
            return conjunct(disjunct(arg0, arg1_0), disjunct(arg0, arg1_1));
        }
        return p;
    }

    private PExp applySimplificationRules(PExp p) {
        int arity = p.getSubExpressions().size();
        switch (arity) {
            case 0:
                return p;
            case 1:
                if (p.getTopLevelOperation().equals("not")) {
                    String arg = p.getSubExpressions().get(0).toString();
                    if (arg.equals("true"))
                        return f;
                    if (arg.equals("false"))
                        return t;
                    return p;
                }
                return p;
            case 2:
                PExp arg0 = p.getSubExpressions().get(0);
                PExp arg1 = p.getSubExpressions().get(1);
                String top = p.getTopLevelOperation();
                String arg0Str = arg0.toString();
                String arg1Str = arg1.toString();
                if (arg0Str.equals(arg1Str)) {
                    switch (top) {
                        case ("and"):
                            return arg0;
                        case ("or"):
                            return arg0;
                        case ("iff"):
                            return t;
                        case ("="):
                            return t;
                        case ("implies"):
                            return t;
                        default:
                            return p;
                    }
                }
                if (arg0Str.equals(("not(" + arg1Str) + ")")) {
                    switch (top) {
                        case ("and"):
                            return f;
                        case ("or"):
                            return t;
                        case ("iff"):
                            return f;
                        case ("implies"):
                            return arg1;
                        default:
                            return p;
                    }
                }
                if (arg0Str.equals("true")) {
                    switch (top) {
                        case ("and"):
                            return arg1;
                        case ("or"):
                            return t;
                        case ("iff"):
                            return arg1;
                        case ("implies"):
                            return arg1;
                        default:
                            return p;
                    }
                }
                if (arg1Str.equals("true")) {
                    switch (top) {
                        case ("and"):
                            return arg0;
                        case ("or"):
                            return t;
                        case ("iff"):
                            return arg0;
                        case ("implies"):
                            return t;
                        default:
                            return p;
                    }
                }
                if (arg0Str.equals("false")) {
                    switch (top) {
                        case ("and"):
                            return f;
                        case ("or"):
                            return arg1;
                        case ("iff"):
                            return negate(arg1);
                        case ("implies"):
                            return t;
                        default:
                            return p;
                    }
                }
                if (arg1Str.equals("false")) {
                    switch (top) {
                        case ("and"):
                            return f;
                        case ("or"):
                            return arg0;
                        case ("iff"):
                            return negate(arg0);
                        case ("implies"):
                            return negate(arg0);
                        default:
                            return p;
                    }
                }
                return p;
            default:
                return p;
        }
    }

    private PExp applyNNFRules(PExp p, int polarity) {
        int arity = p.getSubExpressions().size();
        String top = p.getTopLevelOperation();
        switch (arity) {
            case 0:
                return p;
            case 1:
                if (top.equals("not")) {
                    PExp p1_1 = p.getSubExpressions().get(0);
                    String p1_1t = p1_1.getTopLevelOperation();
                    int p1_1arity = p1_1.getSubExpressions().size();
                    switch (p1_1arity) {
                        case 0:
                            return p;
                        case 1:
                            if (p1_1t.equals("not")) {
                                return p1_1.getSubExpressions().get(0);
                            }
                            return p;
                        case 2:
                            PExp p2_1 = p1_1.getSubExpressions().get(0);
                            PExp p2_2 = p1_1.getSubExpressions().get(1);
                            if (p1_1t.equals("and")) {
                                return disjunct(negate(p2_1), negate(p2_2));
                            }
                            if (p1_1t.equals("or")) {
                                return conjunct(negate(p2_1), negate(p2_2));
                            }
                        default:
                            return p;
                    }
                }
                return p;
            case 2:
                PExp p1_1 = p.getSubExpressions().get(0);
                PExp p1_2 = p.getSubExpressions().get(1);
                switch (top) {
                    case "iff":
                        if (polarity < 0) {
                            return disjunct(conjunct(p1_1, p1_2), conjunct(
                                    negate(p1_1), negate(p1_2)));
                        }
                        return conjunct(disjunct(negate(p1_1), p1_2), disjunct(
                                negate(p1_2), p1_1));
                    case "implies":
                        return disjunct(negate(p1_1), p1_2);
                    default:
                        return p;
                }
            default:
                return p;
        }
    }

    private PExp negate(PExp p) {
        if (p.toString().equals("true")) return f;
        if (p.toString().equals("false")) return t;
        if (p.getTopLevelOperation().equals("not")) {
            return p.getSubExpressions().get(0);
        }
        ArrayList<PExp> args = new ArrayList<>();
        args.add(p);
        return new PSymbol(g.BOOLEAN, null, "not", args);
    }

    private PSymbol disjunct(PExp p, PExp q) {
        ArrayList<PExp> args = new ArrayList<>();
        args.add(p);
        args.add(q);
        return new PSymbol(g.BOOLEAN, null, "or", args);
    }

    private PSymbol conjunct(PExp p, PExp q) {
        ArrayList<PExp> args = new ArrayList<>();
        args.add(p);
        args.add(q);
        return new PSymbol(g.BOOLEAN, null, "and", args);
    }

    // return 0 for proved, 1 nothing else to do, 2 timeout.
    public int prove(long timeoutInMs) {
        eqRoots.clear();
        long endTime = System.currentTimeMillis() + timeoutInMs;
        //log += "After init:" + nl + this.toString() + nl;

        //log += "After processing unit equation clauses:" + nl +
        //termStore.showMergedSymbols() + nl + termStore.showRootMaps() + termStore.showSymbolStore() + this.toString() + nl;
        log += "Init:\n" + stringifyClauseCollection(clauseSet);
        boolean emptyClauseAddedToWo = false;
        boolean timedout = false;
        //while (!emptyClauseAddedToWo && !(clauseSet.isEmpty())) {
        while (!emptyClauseAddedToWo && !(clauseSet.isEmpty() && resolvedClauseSet.isEmpty())) {
            if (System.currentTimeMillis() > endTime) {
                timedout = true;
                break;
            }
            //log += termStore.showRootMaps();
            Clause cur = clauseSet.pollFirst();
            //log += stringifyClauseCollection(clauseSet);
            if (clauseSet.isEmpty()) {
                clauseSet = resolvedClauseSet;
                resolvedClauseSet = new TreeSet<>(new ClauseComp());
                if (cur == null)
                    continue;
            }
            //log += "Removed: " + clauseString(cur);
            cur = cur.updatedClause(termStore);

            if(cur.isTaut) continue;
            emptyClauseAddedToWo = workOff(cur) || termStore.getRootForNullary(2) == 1;
            if(!emptyClauseAddedToWo) emptyClauseAddedToWo = findUnitLiteralContradiction();

            //log += "Worked Off:\n" + stringifyClauseCollection(workedOff) + nl;
            //log += termStore.trie.showUmap();
        }

        if (emptyClauseAddedToWo) {
            if(termStore.getRootForNullary(2) == 1)
                log += "Contradiction through merge of true and false.\n";
            return 0;
        }
        if (timedout)
            return 1;

        log += termStore.showRootMaps();
        log += termStore.showSymbolStore();
        return 2;

    }

    private boolean workOffUnitClause(Clause c) {
        String ac = clauseString(c);
        log += "\nAsserted: " + ac;
        int eRoot = processE(c);
        if(eRoot>0) eqRoots.add(eRoot);
        c = c.updatedClause(termStore);

        /*if (woDisjToWoClauseIndex.containsKey(2)) {
            for (int idx : woDisjToWoClauseIndex.get(2)) {
                Clause up = (workedOff.get(idx).updatedClause(termStore));
                System.err.println(clauseString(workedOff.get(idx))
                        + workedOff.get(idx).disjuncts.toString());
                System.err.println(clauseString(up) + up.disjuncts.toString());
            }
        }*/
        //log += stringifyClauseCollection(workedOff);
        if (c.disjuncts.isEmpty()) {
            log += ac + "is empty\n";
            return true;
        }
        String rat = termStore.trie.contradictDisequalities();
        //if(subs==null) subs = termStore.trie.getUnifier(2,1);
        if (!rat.equals("")) {
            //log += termStore.trie.showUmap() + nl;
            log += rat;
            return true;
        }
        return false;
    }

    // True if contradiction found
    private boolean findUnitLiteralContradiction(){
        applyEquationsToSubExpressions();
        Map<Integer,List<Map<Integer, Integer>>> res = termStore.trie.umapGetAll(2);

        if(res != null && res.containsKey(1)) {
            log += termStore.showRootMaps();
            log += "contradiction found\n";
            Map<Integer,Integer> sub = res.get(1).get(0); // first get is map get, second is list get
            log += "One or more of these are false with\n" + subsToString(sub);
            for(int[] tTerm: termStore.rootMap.getTermsForRoot(1)){
                for(int i: tTerm){
                    if(sub.containsKey(i)){
                        log += "True: " + termStore.termString(tTerm) + "\n";
                    }
                }
            }
            return true;
        }
        return false;
    }
    private boolean workOff(Clause c) {
        String ac = clauseString(c);
        //System.out.println("in wo:" + tag + ac);
        if (c.disjuncts.size() == 0) {
            log += "Empty clause added. WO += " + clauseString(c) + nl;
            return true;
        }
        if (c.isTaut) return false;
        if (woContainmentStringSet.contains(ac)) return false;
        if (c.isUnit()) {
            return workOffUnitClause(c);

        }

        for (int disj : c.disjuncts) {
            if (!woDisjToWoClauseIndex.containsKey(disj)) {
                woDisjToWoClauseIndex.put(disj, new HashSet<>());
            }
            woDisjToWoClauseIndex.get(disj).add(workedOff.size());
        }
        String ll = "WO += " + ac;

        //System.out.print(ll);
        log += ll;
        workedOff.add(c);
        woContainmentStringSet.add(clauseString(c));


        for (int disj : c.disjuncts) {
            // some p(a) = false in glob.  disj is p(x)
            List<Map<Integer, Integer>> subMapList = null;
            if (disj > 0) {
                subMapList = termStore.trie.umapGet(disj, 2); // positive subclause
                if (subMapList != null && !subMapList.isEmpty()) {
                    for (Map<Integer, Integer> submap : subMapList) {
                        if (submap != null && !submap.isEmpty()) {
                            Clause clf = factor(c, submap);
                            if(clf != null && clf.disjuncts.isEmpty()) return true;
                        }
                    }
                }
            } else {
                // if disj is a disequality, look for matches with asserted equations
                List<Map<Integer, Integer>> du = termStore.trie.umapGetForEquation(-disj);
                if (du != null) {
                    for (Map<Integer, Integer> m : du) {
                        Clause clf = factor(c, m);
                        if(clf != null && clf.disjuncts.isEmpty()) return true;
                    }
                }
                subMapList = termStore.trie.umapGet(-disj, 1); // negative subclause
                if (subMapList != null && !subMapList.isEmpty()) {
                    for (Map<Integer, Integer> submap : subMapList) {
                        if (submap != null && !submap.isEmpty()) {
                            Clause clf = factor(c, submap);
                            if(clf != null && clf.disjuncts.isEmpty()) return true;
                        }
                    }
                }
            }


        }

        return false;
    }

    private String subsToString(Map<Integer, Integer> subMap) {
        String m = "";
        if (subMap != null) {
            for (Map.Entry<Integer, Integer> e : subMap.entrySet()) {
                m += termStore.termString(e.getKey()) + "\u21d2";
                String longname = termStore.termString(e.getValue());
                m += longname + nl;
            }
        }
        return m;
    }

    private Clause factor(Clause a, Map<Integer, Integer> subMap) {
        subMap = termStore.trie.prune(subMap);
        String m = subsToString(subMap);
        Clause aSubs = applySubToClause(a, subMap);

        if (aSubs == null)
            return null;
        aSubs = aSubs.updatedClause(termStore);
        String a1 = clauseString(a);
        String a2 = clauseString(aSubs);
        if (aSubs.isTaut)
            return null;
        if (aSubs.disjuncts.size() < a.disjuncts.size()
                && !clauseSet.contains(aSubs)
                && !woContainmentStringSet.contains(clauseString(aSubs))
                && !resolvedClauseSet.contains(aSubs)) {
            String l =
                    "Subst:[\n" + m + "] \n" + "Clause a: " + clauseString(a)
                            + "Factored: " + clauseString(aSubs) + nl;
            //System.out.print(l);
            log += l;
            resolvedClauseSet.add(aSubs);
            //clauseSet.add(aSubs);
            numUniqueResolventsFound++;
            return aSubs;

        }
        return null;
    }

    private Clause applySubToClause(Clause c, Map<Integer, Integer> subMap) {
        Clause rc = new Clause();
        for (int d : c.disjuncts) {
            if (d == 1 || d == -1) {
                rc.addDisjunct(d, true);
                continue;
            }
            boolean isPremise = d < 0;
            int absD = abs(d);
            if (subMap.containsKey(absD)) {
                int rp = subMap.get(absD);
                boolean isConstant = termStore.retrieveSymbol(rp).m_isConstant;
                if (isPremise)
                    rc.addPremise(rp, isConstant);
                else
                    rc.addConclusion(rp, isConstant);
            } else if (subMap.values().contains(d)) {
                rc
                        .addDisjunct(d,
                                termStore.retrieveSymbol(abs(d)).m_isConstant);
            } else {
                cycleLog +=
                        "Disj causing cycle: " + termStore.termString(abs(d));
                Integer alt = applySubToDisj(d, subMap);
                if (alt == null)
                    return null;
                boolean isConstant =
                        termStore.retrieveSymbol(abs(alt)).m_isConstant;
                rc.addDisjunct(alt, isConstant);
            }

        }
        return rc;
    }

    // null if no term exists
    private Integer applySubToDisj(int disj, Map<Integer, Integer> subMap) {
        int abs = abs(disj);
        boolean isPremise = disj < 0;
        if(subMap.containsKey(abs)) {
            if(isPremise) return -subMap.get(abs);
            else return subMap.get(abs);
        }
        SortedSet<int[]> terms = termStore.rootMap.getTermsForRoot(abs);

        if (terms != null) {
            for (int[] term : terms) {
                if (!termStore.termIsRooted(term))
                    continue;
                int[] u = applyUnification(term, subMap, new HashSet<>()); // there is only one possible root for the term after unif

                if (!Arrays.equals(term, u)) {
                    if (u[0] == 0 && u[1] == u[2]) {
                        // u is x = x.  such terms are not kept
                        int r = 1;
                        r = isPremise ? -r : r;
                        return r;
                    }
                    if (termStore.rootMap.containsTerm(u)) {
                        int r = termStore.rootMap.getRootForTerm(u);
                        r = isPremise ? -r : r;
                        return r;
                    } else {

                        // insert this new term, and return its root
                        int r = termStore.putCombination(u);
                        //if(subMap.containsKey(r)) r = subMap.get(r);
                        r = isPremise ? -r : r;
                        return r;
                        //return null;
                    }
                }

            }
        }
        return disj;
    }

    private int abs(int i) {
        if (i < 0)
            return -i;
        return i;
    }

    private void applyEquationsToSubExpressions(){
        for(int r : eqRoots){
            //if(r!=113) continue;
            if(!termStore.isVar(r)) {
                Map<Integer, List<Map<Integer, Integer>>> rm = termStore.trie.umapGetAll(r);
                if (rm != null) {
                    for (Integer k : rm.keySet()) {
                        if (termStore.getRootForNullary(k) != k) continue;
                        for (Map<Integer, Integer> m : rm.get(k)) {
                            // This may not work in all cases.
                            int rM = applySubToDisj(r, m);
                            int kM = applySubToDisj(k,m);
                            rM = termStore.getRootForNullary(rM);
                            kM = termStore.getRootForNullary(kM);
                            if(rM!=kM){
                                log += "SubExprUnifs: merging\n" +
                                        "\t" + termStore.termString(rM) +
                                                "\n\t" + termStore.termString(kM) + nl;
                                termStore.merge(rM,kM);
                            }
                           /* if(m.containsKey(r)){
                                int rrM = m.get(r);
                                if(rrM!=rM){
                                    log += "SubExprUnifs+R: merging\n" +
                                            "\t" + termStore.termString(rrM) +
                                            "\n\t" + termStore.termString(rM) + nl;
                                    termStore.merge(rrM,rM);
                                }
                            }
                            if(m.containsKey(k)){
                                int krM = m.get(k);
                                if(krM!=kM){
                                    log += "SubExprUnifs+R: merging\n" +
                                            "\t" + termStore.termString(krM) +
                                            "\n\t" + termStore.termString(kM) + nl;
                                    termStore.merge(krM,kM);
                                }
                            }
                            */

                        }
                    }
                }
            }
        }
    }
    private int processE(Clause c) {
        int symIdx = c.disjuncts.first();
        int eqResult = -1;
        boolean isPos = 0 <= symIdx;
        SortedSet<int[]> terms = termStore.rootMap.getTermsForRoot(symIdx);
        if (isPos) {
            for (int[] t : terms) {
                if (termStore.retrieveSymbol(t[0]).m_name.equals("=")) {

                    for (int i = 1; i <= 2; ++i) {
                        Map<Integer, List<Map<Integer, Integer>>> rm = termStore.trie.umapGetAll(t[i]);
                        if (rm != null) {
                            for (Integer k : rm.keySet()) {
                                if(termStore.getRootForNullary(k)!=k)continue;
                                for (Map<Integer, Integer> m : rm.get(k)) {
                                    // This may not work in all cases.
                                    Integer a = i ==1 ? applySubToDisj(t[2], m) : applySubToDisj(t[1],m);
                                    Integer b = applySubToDisj(k, m);
                                    a = termStore.getRootForNullary(a);
                                    b = termStore.getRootForNullary(b);
                                    if(a.equals(b)) continue;
                                    log += "\nMap: " + subsToString(m) + "Instantiating " + termStore.termString(t[i]) + " <-> "
                                            + termStore.termString(k) + "\nmerging: " + termStore.termString(a)+
                                            " with " + termStore.termString(b) + "\n";
                                    termStore.merge(a, b);
                                }
                            }
                        }
                    }
                    eqResult = termStore.merge(t[1], t[2]);
                } else {
                    termStore.merge(1, symIdx);
                }
                log += termStore.trie.instantiateTrueAtoms();
            }
        } else {
            termStore.merge(2, abs(symIdx));
        }
        //termStore.trie.refreshUnitPredicates();
        return eqResult;
    }

    private int[] applyUnification(int[] a, Map<Integer, Integer> u, Set<String> termsExplored) {
        if (u.isEmpty())
            return a;
        String tsa = termStore.termString(a);
        termsExplored.add(tsa);
        int[] rInt = new int[a.length];
        Map<Integer, Integer> subsDone = new TreeMap<>();
        for (int i = 0; i < rInt.length; ++i) {
            rInt[i] = a[i];
            if (subsDone.containsKey(rInt[i])) {
                rInt[i] = subsDone.get(rInt[i]);
                continue;
            }
            if(termStore.getRootForNullary(rInt[i])!= rInt[i]){
                return null;
            }
            assert termStore.getRootForNullary(rInt[i]) == rInt[i];
            int depth = 0;
            if (u.containsKey(rInt[i])) {
                rInt[i] = u.get(rInt[i]);
                depth++;
                //continue;
            }

            //Set<Integer> st = new TreeSet<>();
            //termStore.collectSubterms(rInt[i],st);
            //st.retainAll(u.keySet());

            // suppose the term we have is f(x,y) and f(x,y): y
            if (!u.values().contains(rInt[i]) && termStore.isTerm(rInt[i]) && termStore.isInternal(rInt[i])) {
                int[] ft = termStore.rootMap.getLowestOrderTerm(rInt[i]);
                String ftS = termStore.termString(ft);
                if (!termsExplored.contains(ftS) && ft != null && !Arrays.equals(ft, a)) {
                    //System.err.println( ftS + nl +  subsToString(u));
                    int[] ftt = applyUnification(ft, u, termsExplored);
                    if (ftt != null) {
                        if (ftt[0] == 0 && ftt[1] == ftt[2]) {
                            rInt[i] = 1;
                        } else if (termStore.rootMap.containsTerm(ftt)) {
                            rInt[i] = termStore.rootMap.getRootForTerm(ftt);
                        } else {
                            rInt[i] = termStore.putCombination(ftt);
                        }
                    }
                }
            }

            subsDone.put(a[i], rInt[i]);

        }
        return rInt;
    }

    public int appUnif(int t, Map<Integer, Integer> u, int depth) {
        int r = termStore.getRootForNullary(t);
        assert r == t;
        for (int k : u.keySet()) {
            assert termStore.getRootForNullary(k) == k;
        }
        if (u.containsKey(r))
            return u.get(r);
        if (!termStore.isInternal(r))
            return r;
        int[] term = termStore.rootMap.getLowestOrderTerm(r);
        if (term == null)
            return r;
        int[] tSubs = new int[term.length];
        boolean didsub = false;
        if (term != null) {
            for (int i = 0; i < term.length; ++i) {
                tSubs[i] = term[i];
                int dp = 0;
                while (u.containsKey(tSubs[i])) {
                    tSubs[i] = u.get(tSubs[i]);
                    dp++;
                }
                if (termStore.isInternal(tSubs[i]) && tSubs[i] != t) {
                    tSubs[i] = appUnif(tSubs[i], u, 0);
                }
            }
            if (termStore.rootMap.containsTerm(tSubs))
                return termStore.rootMap.getRootForTerm(tSubs);
            else
                return r;//termStore.putCombination(tSubs);
        }

        return r;
    }

    private int appUnifOld(int x, Map<Integer, Integer> u, int depth) {
        if (!termStore.isInternal(x) || !termStore.isTerm(x)) {
            if (u.containsKey(x))
                return u.get(x);
            return x;
        }
        if (depth > 3) {
            System.err.println(depth + ". " + cycleLog + nl
                    + "term being searched:" + termStore.termString(x));
            //System.err.println(log);
        }
        if (depth > 5) {

            return x;
        }

        int[] term = termStore.rootMap.getLowestOrderTerm(x);
        if (term == null)
            return x;
        int[] subsTerm = new int[term.length];
        for (int i = 0; i < term.length; ++i) {
            if (u.containsKey(term[i]))
                subsTerm[i] = u.get(term[i]);
            else if (term[i] != x)
                subsTerm[i] = appUnif(term[i], u, depth + 1);
        }
        if (Arrays.equals(subsTerm, term)) {
            //continue;
            return x;
        }
        if (termStore.rootMap.containsTerm(subsTerm)) {
            return termStore.rootMap.getRootForTerm(subsTerm);
        }
        if (!Arrays.equals(subsTerm, term)) {
            if (subsTerm[0] == 0 && subsTerm[1] == subsTerm[2])
                return 1;
            else
                // form new subexpression
                return termStore.putCombination(subsTerm);
        }

        return x;
    }

    public String clauseString(Clause c) {
        String t = "\n";
        String premises = "";
        String conclusions = "";
        boolean firstpre = true;
        boolean firstconcl = true;
        String sep = ", ";
        for (int d : c.disjuncts) {
            if (d < 0) {
                if (!firstpre) {
                    premises += sep;
                }
                premises += termStore.termString(-d);
                firstpre = false;
            } else {
                if (!firstconcl) {
                    conclusions += sep;
                }
                conclusions += termStore.termString(d);
                firstconcl = false;
            }
        }
        return "{" + premises + "}" + " \u2283 " + "{" + conclusions + "}\n";
    }

    public String toString() {
        String r = "\n";
        /*
        for (PExp p : cnfExpTreeFmt) {
            r += p + "\n";
        }
        String s = "\n";
        for (String cs : cnfSetSets.keySet()) {
            boolean first = true;
            for (String css : cnfSetSets.get(cs).keySet()) {
                if (!first) s += ", ";
                s += css;
                first = false;
            }
            s += "\n";
        }
        String t = "\nClauseSet\n";
         */

        return stringifyClauseCollection(clauseSet);
    }

    public String stringifyClauseCollection(NavigableSet<Clause> cl) {
        String r = "";
        Iterator<Clause> it = cl.iterator();
        while (it.hasNext()) {
            Clause c = it.next();
            r +=
                    "numSyms: " + c.numPositions(termStore) + " isGround: "
                            + c.isGround + " " + clauseString(c);
        }
        return r;
    }
}
