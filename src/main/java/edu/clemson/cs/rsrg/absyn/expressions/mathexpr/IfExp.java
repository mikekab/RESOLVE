/**
 * IfExp.java
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
package edu.clemson.cs.rsrg.absyn.expressions.mathexpr;

import edu.clemson.cs.rsrg.absyn.expressions.Exp;
import edu.clemson.cs.rsrg.parsing.data.Location;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * <p>This is the class for all the mathematical if-else expression objects
 * that the compiler builds using the ANTLR4 AST nodes.</p>
 *
 * @version 2.0
 */
public class IfExp extends MathExp {

    // ===========================================================
    // Member Fields
    // ===========================================================

    /** <p>The testing expression.</p> */
    private final Exp myTestingExp;

    /** <p>The then expression.</p> */
    private final Exp myThenExp;

    /** <p>The else expression.</p> */
    private final Exp myElseExp;

    // ===========================================================
    // Constructors
    // ===========================================================

    /**
     * <p>This constructs an if-else expression.</p>
     *
     * @param l A {@link Location} representation object.
     * @param test An {@link Exp} testing expression.
     * @param thenclause An {@link Exp} then clause expression.
     * @param elseclause An {@link Exp} else clause expression.
     */
    public IfExp(Location l, Exp test, Exp thenclause, Exp elseclause) {
        super(l);
        myTestingExp = test;
        myThenExp = thenclause;
        myElseExp = elseclause;
    }

    // ===========================================================
    // Public Methods
    // ===========================================================

    /**
     * {@inheritDoc}
     */
    @Override
    public final String asString(int indentSize, int innerIndentInc) {
        StringBuffer sb = new StringBuffer();

        printSpace(indentSize, sb);
        sb.append("if ");
        sb.append(myTestingExp.asString(0, innerIndentInc));

        printSpace(indentSize + innerIndentInc, sb);
        sb.append("then ");
        sb.append(myThenExp.asString(0, innerIndentInc));

        if (myElseExp != null) {
            printSpace(indentSize + innerIndentInc, sb);
            sb.append("else ");
            sb.append(myElseExp.asString(indentSize + innerIndentInc,
                    innerIndentInc));
        }

        return sb.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final boolean containsExp(Exp exp) {
        boolean found = false;
        if (myTestingExp != null) {
            found = myTestingExp.containsExp(exp);
        }
        if (!found && myThenExp != null) {
            found = myThenExp.containsExp(exp);
        }
        if (!found && myElseExp != null) {
            found = myElseExp.containsExp(exp);
        }

        return found;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final boolean containsVar(String varName, boolean IsOldExp) {
        Boolean found = false;
        if (myTestingExp != null) {
            found = myTestingExp.containsVar(varName, IsOldExp);
        }
        if (!found && myThenExp != null) {
            found = myThenExp.containsVar(varName, IsOldExp);
        }
        if (!found && myElseExp != null) {
            found = myElseExp.containsVar(varName, IsOldExp);
        }

        return found;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        if (!super.equals(o))
            return false;

        IfExp ifExp = (IfExp) o;

        if (!myTestingExp.equals(ifExp.myTestingExp))
            return false;
        if (!myThenExp.equals(ifExp.myThenExp))
            return false;
        return myElseExp != null ? myElseExp.equals(ifExp.myElseExp)
                : ifExp.myElseExp == null;

    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final boolean equivalent(Exp e) {
        boolean result = e instanceof AltItemExp;

        if (result) {
            IfExp eAsIfExp = (IfExp) e;

            result = myTestingExp.equivalent(eAsIfExp.myTestingExp);
            result &= myThenExp.equivalent(eAsIfExp.myThenExp);
            result &= myElseExp.equivalent(eAsIfExp.myElseExp);
        }

        return result;
    }

    /**
     * <p>Returns this expression's else clause expression.</p>
     *
     * @return The assignment {@link Exp} object.
     */
    public final Exp getElse() {
        return myElseExp;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final List<Exp> getSubExpressions() {
        List<Exp> subExpList = new ArrayList<>();
        subExpList.add(myTestingExp);
        subExpList.add(myThenExp);
        subExpList.add(myElseExp);

        return subExpList;
    }

    /**
     * <p>Returns this expression's testing expression.</p>
     *
     * @return The testing {@link Exp} object.
     */
    public final Exp getTest() {
        return myTestingExp;
    }

    /**
     * <p>Returns this expression's then clause expression.</p>
     *
     * @return The assignment {@link Exp} object.
     */
    public final Exp getThen() {
        return myThenExp;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final int hashCode() {
        int result = super.hashCode();
        result = 31 * result + myTestingExp.hashCode();
        result = 31 * result + myThenExp.hashCode();
        result = 31 * result + (myElseExp != null ? myElseExp.hashCode() : 0);
        return result;
    }

    /**
     * <p>This method applies VC Generator's remember rule.
     * For all inherited programming expression classes, this method
     * should throw an exception.</p>
     *
     * @return The resulting {@link IfExp} from applying the remember rule.
     */
    @Override
    public final Exp remember() {
        Exp testingExp = myTestingExp;
        if (testingExp != null) {
            testingExp = ((MathExp) testingExp).remember();
        }

        Exp thenExp = myThenExp;
        if (thenExp != null) {
            thenExp = ((MathExp) thenExp).remember();
        }

        Exp elseExp = myElseExp;
        if (elseExp != null) {
            elseExp = ((MathExp) elseExp).remember();
        }

        return new IfExp(cloneLocation(), testingExp, thenExp, elseExp);
    }

    /**
     * <p>This method applies the VC Generator's simplification step.</p>
     *
     * @return The resulting {@link MathExp} from applying the simplification step.
     */
    @Override
    public final MathExp simplify() {
        return this.clone();
    }

    // ===========================================================
    // Protected Methods
    // ===========================================================

    /**
     * {@inheritDoc}
     */
    @Override
    protected final Exp copy() {
        Exp newElseExp = null;
        if (myElseExp != null) {
            newElseExp = myElseExp.clone();
        }

        return new IfExp(cloneLocation(), myTestingExp.clone(), myThenExp
                .clone(), newElseExp);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected final Exp substituteChildren(Map<Exp, Exp> substitutions) {
        Exp newElseExp = null;
        if (myElseExp != null) {
            newElseExp = substitute(myElseExp, substitutions);
        }

        return new IfExp(cloneLocation(), substitute(myTestingExp,
                substitutions), substitute(myThenExp, substitutions),
                newElseExp);
    }
}