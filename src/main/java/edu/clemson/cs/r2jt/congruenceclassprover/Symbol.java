package edu.clemson.cs.r2jt.congruenceclassprover;

import edu.clemson.cs.r2jt.rewriteprover.absyn.PSymbol;
import edu.clemson.cs.r2jt.typeandpopulate.MTFunction;
import edu.clemson.cs.r2jt.typeandpopulate.MTNamed;
import edu.clemson.cs.r2jt.typeandpopulate.MTProper;
import edu.clemson.cs.r2jt.typeandpopulate.MTType;

/**
 * Created by Mike on 9/17/2016.
 */
public class Symbol {
    static enum use {constant, variable, type};
    public final use m_usage;
    public final String m_name;
    public final String m_type;
    public final int m_arity;

    public Symbol(String name, use usage, String type, int arity){
        m_name = name;
        m_usage = usage;
        m_type = type;
        m_arity = arity;
    }
    public Symbol(PSymbol p){
        MTType t = p.getType();
        m_type = t.toString();
        if(t instanceof MTFunction){
            MTFunction f = (MTFunction)t;
            m_arity = f.getComponentTypes().size();
        }
        else m_arity = 0;

        if(p.isVariable()){
            m_usage = use.variable;
        }
        else if(t instanceof MTProper || t instanceof MTNamed){
            m_usage = use.type;
        }
        else m_usage = use.constant;

        m_name = p.getTopLevelOperation();
    }
}
