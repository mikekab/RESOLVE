/**
 * Utilities.java
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

import edu.clemson.cs.r2jt.rewriteprover.absyn.PExp;
import edu.clemson.cs.r2jt.rewriteprover.absyn.PSymbol;
import edu.clemson.cs.r2jt.typereasoning.TypeGraph;

import java.util.ArrayList;

/**
 * Created by nabilkabbani on 1/7/16.
 */
public class Utilities {

    final static boolean impliesToAndEq = true;
    public static PExp replacePExp(PExp p, TypeGraph g) {
        String pTop = p.getTopLevelOperation();
        if (pTop.equals("implies")) {
            ArrayList<PExp> args = new ArrayList<PExp>();
            PExp arg1 = replacePExp(p.getSubExpressions().get(0), g);
            PExp arg2 = replacePExp(p.getSubExpressions().get(1), g);
            args.add(arg1);
            args.add(arg2);
            if(impliesToAndEq) {
                PSymbol pAndq = new PSymbol(g.BOOLEAN, null, "and", args);
                args.clear();
                args.add(pAndq);
                args.add(arg1);
                PSymbol pAndqeqP = new PSymbol(g.BOOLEAN, null, "=", args);
                return pAndqeqP;
            } else {
                PSymbol pOrQ = new PSymbol(g.BOOLEAN,null,"or", args);
                args.clear();
                args.add(pOrQ);
                args.add(arg2);
                PSymbol pOrQeqQ = new PSymbol(g.BOOLEAN,null,"=",args);
                return pOrQeqQ;
            }
        }
        else if (pTop.equals("/=")) {
            ArrayList<PExp> args = new ArrayList<PExp>();
            args.add(p.getSubExpressions().get(0));
            args.add(p.getSubExpressions().get(1));
            PSymbol eqExp = new PSymbol(g.BOOLEAN, null, "=", args);
            args.clear();
            args.add(eqExp);
            PSymbol notEqExp = new PSymbol(g.BOOLEAN, null, "not", args);
            return notEqExp;
        }
        return p;
    }
}
