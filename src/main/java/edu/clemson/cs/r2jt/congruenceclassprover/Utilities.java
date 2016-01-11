package edu.clemson.cs.r2jt.congruenceclassprover;

import edu.clemson.cs.r2jt.rewriteprover.absyn.PExp;
import edu.clemson.cs.r2jt.rewriteprover.absyn.PSymbol;
import edu.clemson.cs.r2jt.typereasoning.TypeGraph;

import java.util.ArrayList;

/**
 * Created by nabilkabbani on 1/7/16.
 */
public class Utilities {

    public static PExp replacePExp(PExp p, TypeGraph g){
        String pTop = p.getTopLevelOperation();
        if(pTop.equals("implies")){
            ArrayList<PExp> args = new ArrayList<PExp>();
            PExp arg1 = replacePExp(p.getSubExpressions().get(0),g);
            PExp arg2 = replacePExp(p.getSubExpressions().get(1),g);
            args.add(arg1);
            args.add(arg2);
            PSymbol pAndq = new PSymbol(g.BOOLEAN,null,"and",args);
            args.clear();
            args.add(pAndq);
            args.add(arg1);
            PSymbol pAndqeqQ = new PSymbol(g.BOOLEAN,null,"=",args);
            return pAndqeqQ;
        }
        else if(pTop.equals("/=")){
            ArrayList<PExp> args = new ArrayList<PExp>();
            args.add(p.getSubExpressions().get(0));
            args.add(p.getSubExpressions().get(1));
            PSymbol eqExp =
                    new PSymbol(g.BOOLEAN, null, "=", args);
            args.clear();
            args.add(eqExp);
            PSymbol notEqExp =
                    new PSymbol(g.BOOLEAN, null, "not",
                            args);
            return notEqExp;
        }
        return p;
    }
}
