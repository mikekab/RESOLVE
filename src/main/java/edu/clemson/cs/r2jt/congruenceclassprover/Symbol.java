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
    public final boolean m_isType;
    public final boolean m_isConstant;
    public final boolean m_internal;
    public final int m_arity;
    public final String m_name;
    public final String m_type;


    public Symbol(String name, String type, int arity, boolean isConstant, boolean isType){
        m_name = name;
        m_type = type;
        m_arity = arity;
        m_isConstant = isConstant;
        m_isType = isType;
        m_internal = true;
    }
    public Symbol(PSymbol p){
        MTType t = p.getType();
        String ts = t.toString();
        int arity = 0;
        boolean is_constant = true;
        boolean is_type = false;
        String name = p.getTopLevelOperation();
        if(t instanceof MTFunction){
            MTFunction f = (MTFunction)t;
            arity = f.getComponentTypes().size();
        }
        else if(p.getSubExpressions().size()>0){
            arity = p.getSubExpressions().size();
        }

        if(p.quantification.equals(PSymbol.Quantification.FOR_ALL)){
            is_constant = false;
        }


        this.m_name = name;
        this.m_type = ts;
        this.m_arity = arity;
        this.m_isConstant = is_constant;
        this.m_isType = is_type;
        m_internal = false;
    }
}
