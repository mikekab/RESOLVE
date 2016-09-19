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

    HashMap<CnfFlatClause, Integer> clauseSet;
    TypeGraph g;
    List<PExp> cnfExpTreeFmt;
    Map<String,Map<String,PExp>> cnfSetSets;
    PExp t;
    PExp f;
    MTType z;
    MTType n;
    int var_counter = 0;

    public ClauseSet(TypeGraph graph, MTType Z, MTType N) {
        g = graph;
        z = Z;
        n = N;
        clauseSet = new HashMap<>(1024);
        cnfExpTreeFmt = new ArrayList<>();
        t = new PSymbol(g.BOOLEAN, null, "true");
        f = new PSymbol(g.BOOLEAN, null, "false");
        cnfSetSets = new HashMap<>();
    }
    private void addTreeFmtToSetofSets(PExp p, TreeMap<String, PExp> clauseElem){
        String top = p.getTopLevelOperation();
        switch (top){
            case "and":
                addTreeFmtToSetofSets(p.getSubExpressions().get(0), clauseElem);
                addTreeFmtToSetofSets(p.getSubExpressions().get(1), new TreeMap<String, PExp>());
                break;
            case "or":
                splitOrs(p,clauseElem);
                cnfSetSets.put(clauseElem.keySet().toString(),clauseElem);
                break;
            default:
                clauseElem.put(p.toString(),p);
                // could do complement check
                cnfSetSets.put(clauseElem.keySet().toString(),clauseElem);
        }

    }

    // remove or, return map of literals.
    // Ex: a or (b or (c or d)) returns collection a,b,c,d
    private void splitOrs(PExp p, TreeMap<String,PExp> col){
        String top = p.getTopLevelOperation();
        if(top.equals("or")){
            splitOrs(p.getSubExpressions().get(0),col);
            splitOrs(p.getSubExpressions().get(1),col);
        }
        else col.put(p.toString(),p);
    }
    public void addVC(VC vc) {
        cnfExpTreeFmt.addAll(vc.getAntecedent().getMutableCopy());
        for (PExp p : vc.getConsequent().getMutableCopy()) {
            cnfExpTreeFmt.add(negate(p));
        }
        cnfExpTreeFmt = Utilities.convertList(cnfExpTreeFmt, g, z, n);
        cnfExpTreeFmt = simplifyList(cnfExpTreeFmt);
        for(PExp p : cnfExpTreeFmt){
            addTreeFmtToSetofSets(p, new TreeMap<String, PExp>());
        }
    }

    public void addClause(PExp p) {
        p = Utilities.replacePExp(p, g, z, n);
        p = multipassSimpApplier(p);
        p = multipassNNFApplier(p);
        p = multipassCNFApplier(p);
        cnfExpTreeFmt.add(p);
        addTreeFmtToSetofSets(p,new TreeMap<String, PExp>());

    }

    private List<PExp> simplifyList(List<PExp> clist) {
        HashMap<String, PExp> conj = new HashMap<>();
        // simplify each element
        for (PExp p : clist) {
            PExp p_prime = multipassSimpApplier(p);
            p_prime = multipassNNFApplier(p_prime);
            String p_p_S = p_prime.toString();
            if (p_p_S.equals("false")) {
                clist.clear();
                clist.add(f);
                return clist;
            }
            if (!p_p_S.equals("true")) {
                conj.put(p_p_S, p_prime);
            }
        }
        clist.clear();
        // apply "and" rules between elements.
        // Only have to check for complements, rest done above.
        for (String ps : conj.keySet()) {
            String comp = "not(" + ps + ")";
            if (conj.containsKey(comp)) {
                clist.add(f);
                return clist;
            }
        }
        if (conj.isEmpty()) {
            clist.add(f);
        } else {
            clist.addAll(conj.values());
        }
        return clist;
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
            p = depthFirstRecursiveNNFRuleApplier(p,1);
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
            argsA.add(depthFirstRecursiveNNFRuleApplier(arg,polarity));
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
    private PExp applyCNFRules(PExp p){
        if(!p.getTopLevelOperation().equals("or")) return p;
        PExp arg0 = p.getSubExpressions().get(0);
        PExp arg1 = p.getSubExpressions().get(1);
        if(arg0.getTopLevelOperation().equals("and")){
            PExp arg0_0 = arg0.getSubExpressions().get(0);
            PExp arg0_1 = arg0.getSubExpressions().get(1);
            return conjunct(disjunct(arg1,arg0_0),disjunct(arg1,arg0_1));
        }
        if(arg1.getTopLevelOperation().equals("and")){
            PExp arg1_0 = arg1.getSubExpressions().get(0);
            PExp arg1_1 = arg1.getSubExpressions().get(1);
            return conjunct(disjunct(arg0,arg1_0),disjunct(arg0,arg1_1));
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
                switch (top){
                    case "iff":
                        if(polarity < 0){
                            return disjunct(conjunct(p1_1,p1_2),conjunct(negate(p1_1),negate(p1_2)));
                        }
                        return conjunct(disjunct(negate(p1_1),p1_2),disjunct(negate(p1_2),p1_1));
                    case "implies":
                        return disjunct(negate(p1_1),p1_2);
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

    public String toString() {
        String r = "\n";
        for (PExp p : cnfExpTreeFmt) {
            r += p + "\n";
        }
        String s = "\n";
        for (String cs : cnfSetSets.keySet()){
            boolean first = true;
            for(String css : cnfSetSets.get(cs).keySet()){
                if(!first) s += ", ";
                s += css;
                first = false;
            }
            s += "\n";
        }
        return r + s;
    }
}
