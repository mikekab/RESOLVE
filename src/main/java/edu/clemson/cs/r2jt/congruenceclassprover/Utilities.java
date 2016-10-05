/**
 * Utilities.java
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
import edu.clemson.cs.r2jt.typereasoning.TypeGraph;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by Mike on 2/1/2016.
 * Transformation that apply to both expressions in both VC and Theorems
 */
public class Utilities {

    public static PExp replacePExp(PExp pe, TypeGraph g, MTType z, MTType n) {
        ArrayList<PExp> argList = new ArrayList<PExp>();
        ArrayList<PExp> argsTemp = new ArrayList<PExp>();
        PSymbol p = (PSymbol)pe;
        for (PExp pa : p.getSubExpressions()) {
            argList.add(replacePExp(pa, g, z, n));
        }
        // Somehow hidden characters are getting introduced.
        String pTop = p.getTopLevelOperation().replaceAll("\\p{Cc}", "");
        // Every symbol is rewritten by this method.
        if (pTop.equals("/=")) {
            PSymbol eqExp = new PSymbol(g.BOOLEAN, null, "=", argList);
            argList.clear();
            argList.add(eqExp);
            return new PSymbol(g.BOOLEAN, null, "not", argList);
        }
        else if(pTop.equals("=")&& argList.get(0).getType().toString().equals("B")){
            return new PSymbol(g.BOOLEAN,null,"iff",argList);
        }
        else if (pTop.equals(">=")) {
            argsTemp.add(argList.get(1));
            argsTemp.add(argList.get(0));
            return new PSymbol(g.BOOLEAN, null, "<=", argsTemp);
        }
        else if (pTop.equals("<") && z != null && n != null
                && argList.get(0).getType().isSubtypeOf(z)
                && argList.get(1).getType().isSubtypeOf(z)) {
            // x < y to x + 1 <= y
            argsTemp.add(argList.get(0));
            argsTemp.add(new PSymbol(n, null, "1"));
            PSymbol plus1 =
                    new PSymbol(argList.get(0).getType(), null, "+"
                            + argList.get(0).getType().toString(), argsTemp);
            argsTemp.clear();
            argsTemp.add(plus1);
            argsTemp.add(argList.get(1));
            return new PSymbol(p.getType(), p.getTypeValue(), "<=", argsTemp);
        }
        else if (pTop.equals(">") && z != null && n != null
                && argList.get(0).getType().isSubtypeOf(z)
                && argList.get(1).getType().isSubtypeOf(z)) {
            // x > y to y + 1 <= x
            argsTemp.add(argList.get(1));
            argsTemp.add(new PSymbol(n, null, "1"));
            PSymbol plus1 =
                    new PSymbol(argList.get(1).getType(), null, "+"
                            + argList.get(1).getType().toString(), argsTemp);
            argsTemp.clear();
            argsTemp.add(plus1);
            argsTemp.add(argList.get(0));
            return new PSymbol(p.getType(), p.getTypeValue(), "<=", argsTemp);
        }
        else if (z != null && pTop.equals("-")
                && p.getSubExpressions().size() == 2) {
            // x - y to x + (-y)
            argsTemp.add(argList.get(1));
            PSymbol minusY =
                    new PSymbol(p.getType(), null,
                            "-" + p.getType().toString(), argsTemp);
            argsTemp.clear();
            argsTemp.add(argList.get(0));
            argsTemp.add(minusY);
            return new PSymbol(p.getType(), null, "+" + p.getType().toString(),
                    argsTemp);
        }
        // New: 5/8/16. Tag operators with range type if they aren't quantified.
 /*       else if (argList.size() > 0 ) {
            if (((PSymbol) p).quantification
                    .equals(PSymbol.Quantification.NONE))
                pTop += p.getType().toString();
            return new PSymbol(p.getType(), p.getTypeValue(), pTop, argList,
                    ((PSymbol) p).quantification);
        }*/
        if(argList.isEmpty()){
            return new PSymbol(p.getType(), p.getTypeValue(), pTop, p.quantification);
        }
        return new PSymbol(p.getType(), p.getTypeValue(), pTop,
                argList);
    }
    public static List<PExp> convertList(List<PExp> list, TypeGraph g, MTType z, MTType n){
        ArrayList<PExp> rlist = new ArrayList<>();
        for(PExp p : list){
            rlist.add(replacePExp(p,g,z,n));
        }
        return rlist;
    }
}