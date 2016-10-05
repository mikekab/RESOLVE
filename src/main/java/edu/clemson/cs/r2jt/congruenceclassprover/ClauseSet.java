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

    Set<Clause> groundUnitClauseSet;
    Set<Clause> clauseSet;
    TypeGraph g;
    List<PExp> cnfExpTreeFmt;
    Map<String, Map<String, PExp>> cnfSetSets;
    PExp t;
    PExp f;
    MTType z;
    MTType n;
    TermStore termStore;

    public ClauseSet(TypeGraph graph, MTType Z, MTType N) {
        g = graph;
        z = Z;
        n = N;
        groundUnitClauseSet = new HashSet<>(1024);
        clauseSet = new HashSet<>(1024);
        cnfExpTreeFmt = new ArrayList<>();
        t = new PSymbol(g.BOOLEAN, null, "true");
        f = new PSymbol(g.BOOLEAN, null, "false");
        cnfSetSets = new HashMap<>();
        termStore = new TermStore();
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
                    clauseElem = renameVarsInClause(clauseElem);
                    cnfSetSets.put(clauseElem.keySet().toString(), clauseElem);
                }
                break;
            default:
                if (!clauseElem.containsKey("true")) {
                    clauseElem.put(p.toString(), p);
                    clauseElem = renameVarsInClause(clauseElem);
                    cnfSetSets.put(clauseElem.keySet().toString(), clauseElem);
                }

        }

    }

    private TreeMap<String, PExp> renameVarsInClause(TreeMap<String, PExp> clause) {
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
            name = "@" + name + "_" + curCount;
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
            if (col.containsKey(("not(" + p.toString() + ")")) ||
                    (top.equals("not") && col.containsKey(p.getSubExpressions().get(0).toString()))) {
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
                if ( c.isGround && c.disjuncts.size()==1) {
                    groundUnitClauseSet.add(c);
                } else {
                    Set<Clause> subsumed = new HashSet<>();
                    for(Clause cl : clauseSet){
                        if(cl.disjuncts.containsAll(c.disjuncts)){
                            subsumed.add(cl);
                        }
                    }
                    clauseSet.removeAll(subsumed);
                    clauseSet.add(c);
                }
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
        if (!p.getTopLevelOperation().equals("or")) return p;
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
                    if (arg.equals("true")) return f;
                    if (arg.equals("false")) return t;
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
                            return disjunct(conjunct(p1_1, p1_2), conjunct(negate(p1_1), negate(p1_2)));
                        }
                        return conjunct(disjunct(negate(p1_1), p1_2), disjunct(negate(p1_2), p1_1));
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
        for (Clause c : groundUnitClauseSet) {
            t += clauseString(c);
        }
        for (Clause c : clauseSet) {
            t += clauseString(c);
        }


        return r + s + t;
    }
}
