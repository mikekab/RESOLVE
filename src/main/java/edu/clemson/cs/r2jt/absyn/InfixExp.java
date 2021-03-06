/**
 * InfixExp.java
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
package edu.clemson.cs.r2jt.absyn;

import edu.clemson.cs.r2jt.collections.List;
import java.util.concurrent.atomic.AtomicInteger;
import edu.clemson.cs.r2jt.collections.Iterator;
import edu.clemson.cs.r2jt.data.Location;
import edu.clemson.cs.r2jt.data.PosSymbol;
import edu.clemson.cs.r2jt.data.Symbol;
import edu.clemson.cs.r2jt.init.CompileEnvironment;

public class InfixExp extends AbstractFunctionExp {

    /** The location member. */
    private Location location;

    /** The left member. */
    private Exp left;

    /** The opName member. */
    private PosSymbol opName;

    /** The right member. */
    private Exp right;

    public InfixExp() {
    // Empty
    }

    @Override
    public int getQuantification() {
        return VarExp.NONE;
    }

    public InfixExp(Location location, Exp left, PosSymbol opName, Exp right) {
        this.location = location;
        this.left = left;
        this.opName = opName;
        this.right = right;
    }

    public boolean equivalent(Exp e) {
        boolean retval = e instanceof InfixExp;

        if (retval) {
            InfixExp eAsInfix = (InfixExp) e;
            retval =
                    posSymbolEquivalent(opName, ((InfixExp) e).opName)
                            && left.equivalent(eAsInfix.getLeft())
                            && right.equivalent(eAsInfix.getRight());
        }

        return retval;
    }

    public Exp substituteChildren(java.util.Map<Exp, Exp> substitutions) {
        Exp retval;

        retval =
                new InfixExp(location, substitute(left, substitutions), opName,
                        substitute(right, substitutions));

        retval.setMathType(getMathType());
        retval.setMathTypeValue(getMathTypeValue());

        return retval;
    }

    /** Returns the value of the location variable. */
    @Override
    public Location getLocation() {
        return location;
    }

    /** Returns the value of the left variable. */
    public Exp getLeft() {
        return left;
    }

    /** Returns the value of the opName variable. */
    public PosSymbol getOpName() {
        return opName;
    }

    /** Returns the value of the right variable. */
    public Exp getRight() {
        return right;
    }

    /** Sets the location variable to the specified value. */
    public void setLocation(Location location) {
        this.location = location;
    }

    /** Sets the left variable to the specified value. */
    public void setLeft(Exp left) {
        this.left = left;
    }

    /** Sets the opName variable to the specified value. */
    public void setOpName(PosSymbol opName) {
        this.opName = opName;
    }

    /** Sets the right variable to the specified value. */
    public void setRight(Exp right) {
        this.right = right;
    }

    /** Accepts a ResolveConceptualVisitor. */
    public void accept(ResolveConceptualVisitor v) {
        v.visitInfixExp(this);
    }

    /** Returns a formatted text string of this class. */
    public String asString(int indent, int increment) {

        StringBuffer sb = new StringBuffer();

        printSpace(indent, sb);
        sb.append("InfixExp\n");

        if (left != null) {
            sb.append(left.asString(indent + increment, increment));
        }

        if (opName != null) {
            sb.append(opName.asString(indent + increment, increment));
        }

        if (right != null) {
            sb.append(right.asString(indent + increment, increment));
        }

        return sb.toString();
    }

    /** Returns a formatted text string of this class. */
    public String toString(int indent) {
        //	if(env.flags.isFlagSet(Verifier.FLAG_LISTVCS_VC)){return toAltString(indent);}
        //	if(env.flags.isFlagSet(Verifier.FLAG_ISABELLE_VC)){return toIsabelleString(indent);};

        StringBuffer sb = new StringBuffer();

        if (left != null) {
            if (opName.toString().equals("implies")) {
                //printSpace(indent, sb);
                sb.append("(" + left.toString(0) + " ");
            }
            else {
                sb.append("(" + left.toString(0) + " ");
            }
        }

        if (opName != null) {

            if (opName.toString().equals("and")) {
                //sb.append(opName.toString() + "\n");
                sb.append(opName.toString() + " ");
            }
            else if (opName.toString().equals("and")) {
                sb.append(opName.toString() + " ");
            }
            else
                sb.append(opName.toString() + " ");
        }

        if (right != null) {
            if (opName.toString().equals("implies")) {
                /* This is an implication */
                if (right instanceof InfixExp
                        && !((InfixExp) right).getOpName().toString().equals(
                                "implies")) {
                    /* And the right Exp is NOT an implication */
                    //sb.append("\n");
                    sb.append(" ");
                    //printSpace(indent + 4, sb);
                    sb.append(right.toString(indent + 4) + ")");
                }
                else if (right instanceof InfixExp) {
                    /* And the right is an Implication, but could 
                     * contain an implication or is an and/or statement
                     */
                    //sb.append("\n");
                    sb.append(" ");
                    sb.append(right.toString(indent) + ")");
                }
                else
                    //sb.append("\n" + right.toString(indent + 4) + ")");
                    sb.append(" " + right.toString(indent + 4) + ")");
            }
            else /* This is Not an Implication */
            if (right instanceof InfixExp
                    && !((InfixExp) right).getOpName().toString().equals(
                            "implies")) {
                /* And the right Exp is NOT an implication */
                sb.append(right.toString(indent) + ")");

            }
            else if (right instanceof InfixExp) {
                /* And the right is an Implication, but could 
                 * contain an implication or is an and/or statement
                 */
                //sb.append("\n" + right.toString(indent) + ")");
                sb.append(" " + right.toString(indent) + ")");
            }
            else
                sb.append(right.toString(0) + ")");
        }

        return sb.toString();
    }

    /** Returns a formatted text string of this class. */
    public String toAltString(int indent) {
        return toAltString(indent, new AtomicInteger(0));
    }

    public String toAltString(int indent, AtomicInteger mycount) {

        StringBuffer sb = new StringBuffer();

        printSpace(indent, sb);

        if (left != null) {
            if (opName.toString().equals("implies")) {

                sb.append("" + left.toString(0) + "");
            }
            else {
                if (opName.toString().equals("and")) {
                    if (left instanceof InfixExp
                            && ((InfixExp) left).getOpName().toString().equals(
                                    "and")) {
                        sb.append(""
                                + ((InfixExp) left).toAltString(0, mycount)
                                + "");
                    }
                    else {
                        int count = mycount.intValue();
                        count++;
                        mycount.set(count);
                        sb.append(count + ": " + left.toString(0) + "");
                    }
                }
                else if (left instanceof InfixExp) {
                    sb.append("" + ((InfixExp) left).toAltString(0, mycount)
                            + "");
                }
                else {
                    sb.append("(" + left.toString(0) + " ");
                }
            }
        }

        if (opName != null) {
            if (opName.toString().equals("and")) {
                sb.append("\n");
            }
            else
                sb.append(opName.toString() + " ");
        }

        if (right != null) {
            if (opName.toString().equals("implies")) {
                /* This is an implication */
                if (right instanceof InfixExp
                        && !((InfixExp) right).getOpName().toString().equals(
                                "implies")) {
                    /* And the right Exp is NOT an implication */
                    sb.append("\n");
                    printSpace(indent, sb);
                    sb.append(((InfixExp) right).toAltString(indent, mycount)
                            + "");
                }
                else if (right instanceof InfixExp) {
                    /* And the right is an Implication, but could 
                     * contain an implication or is an and/or statement
                     */
                    sb.append("\n");
                    sb.append(((InfixExp) right).toAltString(indent, mycount)
                            + "");
                }
                else
                    sb.append("\n" + right.toString(indent) + "");
            }
            else /* This is Not an Implication */
            if (right instanceof InfixExp
                    && !((InfixExp) right).getOpName().toString().equals(
                            "implies")) {
                if (opName.toString().equals("and")) {
                    if (((InfixExp) right).getOpName().toString().equals("and")) {
                        sb.append(""
                                + ((InfixExp) right).toAltString(indent,
                                        mycount) + "");
                    }
                    else {
                        int count = mycount.intValue();
                        count++;
                        mycount.set(count);
                        sb.append(count + ": " + right.toString(indent) + "");
                    }
                }
                else
                    /* And the right Exp is NOT an implication */
                    sb.append(right.toString(indent) + ")");

            }
            else if (right instanceof InfixExp) {
                /* And the right is an Implication, but could 
                 * contain an implication or is an and/or statement
                 */
                if (((InfixExp) right).getOpName().toString().equals("and")) {
                    sb.append(""
                            + ((InfixExp) right).toAltString(indent, mycount)
                            + "");
                }
                else {
                    int count = mycount.intValue();
                    count++;
                    mycount.set(count);
                    sb.append("" + count + ": " + right.toString(indent) + "");
                }
            }
            else {
                if (opName.toString().equals("and")) {
                    int count = mycount.intValue();
                    count++;
                    mycount.set(count);
                    sb.append("" + count + ": " + right.toString(0) + "");
                }
                else
                    sb.append(right.toString(0) + ")");

            }
        }

        return sb.toString();
    }

    /** Returns a formatted text string of this class. */
    public String printLocation(final AtomicInteger mycount) {

        StringBuffer sb = new StringBuffer();

        if (left != null) {
            if (opName.toString().equals("implies")) {

            }
            else {
                if (opName.toString().equals("and")) {
                    if (left instanceof InfixExp
                            && ((InfixExp) left).getOpName().toString().equals(
                                    "and")) {
                        sb.append("" + ((InfixExp) left).printLocation(mycount)
                                + "");
                    }
                    else {
                        int count = mycount.intValue();
                        count++;
                        mycount.set(count);
                        if (left.getLocation() != null) {
                            sb.append("\n" + mycount + ": "
                                    + left.getLocation() + ": "
                                    + left.getLocation().getDetails());
                        }
                        else {
                            sb.append("" + mycount + ": ");
                        }
                    }
                }
            }
        }

        if (opName != null) {
            if (!opName.toString().equals("and")) {
                int count = mycount.intValue();
                count++;
                mycount.set(count);
                if (left.getLocation() != null) {
                    sb.append("\n" + mycount + ": " + this.getLocation() + ": "
                            + this.getLocation().getDetails());
                }
                else {
                    sb.append("" + mycount + ": ");
                }
            }
        }

        if (right != null) {
            if (!opName.toString().equals("implies")) {
                if (right instanceof InfixExp
                        && !((InfixExp) right).getOpName().toString().equals(
                                "implies")) {
                    if (opName.toString().equals("and")) {
                        if (((InfixExp) right).getOpName().toString().equals(
                                "and")) {
                            sb.append(""
                                    + ((InfixExp) right).printLocation(mycount)
                                    + "");
                        }
                        else {
                            int count = mycount.intValue();
                            count++;
                            mycount.set(count);
                            if (right.getLocation() != null) {
                                sb.append("\n" + mycount + ": "
                                        + right.getLocation() + ": "
                                        + right.getLocation().getDetails());
                            }
                            else {
                                sb.append("\n" + mycount + ": ");
                            }
                        }
                    }
                }
                else {
                    int count = mycount.intValue();
                    count++;
                    mycount.set(count);
                    if (right.getLocation() != null) {
                        sb.append("\n" + mycount + ": " + right.getLocation()
                                + ": " + right.getLocation().getDetails());
                    }
                    else {
                        sb.append("\n" + mycount + ": ");
                    }
                }
            }
        }

        return sb.toString();
    }

    /** Returns a formatted text string of this class. */
    public String toIsabelleString(int indent) {

        StringBuffer sb = new StringBuffer();

        printSpace(indent, sb);

        if (left != null) {
            if (opName.toString().equals("implies")) {
                sb.append("" + left.toString(0) + "");
            }
            else {
                if (opName.toString().equals("and"))
                    sb.append("" + left.toString(0) + "");
                else
                    sb.append("(" + left.toString(0) + " ");
            }
        }

        if (opName != null) {
            if (opName.toString().equals("and")) {
                sb.append(";\n");
            }
            else if (opName.toString().equals("and")) {
                sb.append(" & ");
            }
            else if (opName.toString().equals("implies")) {
                sb.append(" --> ");
            }
            else if (opName.toString().equals("o")) {
                sb.append(" * ");
            }
            else
                sb.append(opName.toString() + " ");
        }

        if (right != null) {
            if (opName.toString().equals("implies")) {
                /* This is an implication */
                if (right instanceof InfixExp
                        && !((InfixExp) right).getOpName().toString().equals(
                                "implies")) {
                    /* And the right Exp is NOT an implication */
                    sb.append("\n");
                    printSpace(indent, sb);
                    sb.append(right.toString(indent) + "");
                }
                else if (right instanceof InfixExp) {
                    /* And the right is an Implication, but could 
                     * contain an implication or is an and/or statement
                     */
                    sb.append("\n");
                    sb.append(right.toString(indent) + "");
                }
                else
                    sb.append("\n" + right.toString(indent) + "");
            }
            else /* This is Not an Implication */
            if (right instanceof InfixExp
                    && !((InfixExp) right).getOpName().toString().equals(
                            "implies")) {
                if (opName.toString().equals("and"))
                    sb.append(right.toString(indent) + "");
                else
                    /* And the right Exp is NOT an implication */
                    sb.append(right.toString(indent) + ")");

            }
            else if (right instanceof InfixExp) {
                /* And the right is an Implication, but could 
                 * contain an implication or is an and/or statement
                 */
                if (opName.toString().equals("and"))
                    sb.append("\n" + right.toString(indent) + "");
                else
                    sb.append("\n" + right.toString(indent) + "");
            }
            else {
                if (opName.toString().equals("and"))
                    sb.append(right.toString(0) + "");
                else
                    sb.append(right.toString(0) + ")");

            }
        }

        return sb.toString();
    }

    public String splitToString(int indent) {
        StringBuffer sb = new StringBuffer();
        sb.append(left.toString(0));
        sb.append("\n______________\n");
        sb.append(right.toString(0));
        return sb.toString();
    }

    public Exp getAssumptions() {
        if (this.opName.toString().equals("implies")
                || this.opName.toString().equals("and")) {
            if (left instanceof InfixExp) {
                left = ((InfixExp) left).getAssumptions();
            }
            if (right instanceof InfixExp) {
                right = ((InfixExp) right).getAssumptions();
            }
            return new InfixExp(null, left, createPosSymbol("and"), right);
        }
        else
            return this;
    }

    public Exp getAssertions() {
        if (opName.toString().equals("and")) {
            Exp tmpLeft, tmpRight;
            if (left instanceof InfixExp)
                tmpLeft = ((InfixExp) left).getAssertions();
            else
                tmpLeft = left;

            if (right instanceof InfixExp)
                tmpRight = ((InfixExp) right).getAssertions();
            else
                tmpRight = right;

            return getMathType().getTypeGraph().formConjunct(tmpLeft, tmpRight);
        }
        else if (!(opName.toString().equals("implies"))) {
            return this;
        }
        return null;
    }

    /** Returns a formatted text string of this class. */
    public List<InfixExp> split(Exp assumpts, boolean single) {
        List<InfixExp> lst = new List<InfixExp>();
        Exp tmpLeft, tmpRight;
        if (opName.toString().equals("and")) {
            if (left != null)
                lst.addAll(left.split(assumpts, single));
            if (right != null)
                lst.addAll(right.split(assumpts, single));
        }
        else if (opName.toString().equals("implies")) {
            if (left instanceof InfixExp) {
                tmpLeft = ((InfixExp) left).getAssumptions();
                lst = left.split(assumpts, false);
            }
            else
                tmpLeft = left;

            if (assumpts != null)
                tmpLeft =
                        getMathType().getTypeGraph().formConjunct(assumpts,
                                tmpLeft);

            if (right instanceof InfixExp) {
                tmpRight = ((InfixExp) right).getAssertions();

                lst = right.split(tmpLeft, single);

                if (tmpRight == null)
                    return lst;
            }
            else {
                tmpRight = right;

                if (!(tmpLeft == null || tmpRight == null)) {
                    lst.add(new InfixExp(null, tmpLeft,
                            createPosSymbol("implies"), tmpRight));
                }
            }

        }
        else if (single) {
            lst.add(new InfixExp(null, assumpts, createPosSymbol("implies"),
                    this));
        }

        return lst;

    }

    InfixExp formAndExp(Exp A, Exp B) {
        InfixExp AndStmt = new InfixExp();
        AndStmt.setOpName(createPosSymbol("and"));
        AndStmt.setLeft((Exp) Exp.clone(A));
        AndStmt.setRight((Exp) Exp.clone(B));
        return AndStmt;
    }

    /** Returns true if the variable is found in any sub expression   
        of this one. **/
    public boolean containsVar(String varName, boolean IsOldExp) {
        Boolean found = false;
        if (left != null) {
            found = left.containsVar(varName, IsOldExp);
        }
        if (!found && right != null) {
            found = right.containsVar(varName, IsOldExp);
        }
        return found;
    }

    public Object clone() {
        InfixExp clone = new InfixExp();
        if (left == null || right == null)
            return this;
        clone.setLeft((Exp) Exp.clone(left));
        clone.setRight((Exp) Exp.clone(right));
        if (this.location != null)
            clone.setLocation((Location) location.clone());
        clone.setOpName(opName);
        clone.setMathType(getMathType());
        clone.setMathTypeValue(getMathTypeValue());
        return clone;
    }

    public List<Exp> getSubExpressions() {
        List<Exp> list = new List<Exp>();
        list.add(left);
        list.add(right);
        return list;
    }

    public void setSubExpression(int index, Exp e) {
        switch (index) {
        case 0:
            left = e;
            break;
        case 1:
            right = e;
            break;
        }
    }

    public boolean shallowCompare(Exp e2) {
        if (!(e2 instanceof InfixExp)) {
            return false;
        }
        if (!(opName.equals(((InfixExp) e2).getOpName().getName()))) {
            return false;
        }
        return true;
    }

    public void prettyPrint() {
        System.out.print("(");
        left.prettyPrint();
        System.out.print(" " + opName.getName() + " ");
        right.prettyPrint();
        System.out.print(")");
    }

    public Exp replace(Exp old, Exp replacement) {
        if (!(old instanceof InfixExp)) {
            InfixExp newExp = new InfixExp();
            newExp.setLocation(this.location);
            newExp.setMathType(getMathType());
            newExp.setMathTypeValue(getMathTypeValue());

            newExp.setOpName(this.opName);
            if (left == null || right == null)
                return this;

            newExp.setLeft((Exp) Exp.clone(this.getLeft()));
            newExp.setRight((Exp) Exp.clone(this.getRight()));

            Exp lft = Exp.replace(newExp.getLeft(), old, replacement);
            Exp rgt = Exp.replace(newExp.getRight(), old, replacement);
            if (lft != null) {
                //String lf = lft.toString(1);
                newExp.setLeft(lft);
            }
            if (rgt != null) {
                //String rg = rgt.toString(1);
                newExp.setRight(rgt);
            }

            return newExp;
        }
        else
            return this;
    }

    public Exp remember() {
        if (left instanceof OldExp)
            this.setLeft(((OldExp) (left)).getExp().remember());
        if (right instanceof OldExp)
            this.setRight(((OldExp) (right)).getExp().remember());
        if (left != null)
            left = left.remember();
        if (right != null)
            right = right.remember();

        return this;
    }

    public InfixExp simplifyComponents() {
        InfixExp simplified = ((InfixExp) Exp.clone(this));
        simplified.setLeft(simplified.getLeft().simplify());
        simplified.setRight(simplified.getRight().simplify());
        return simplified;
    }

    public Exp simplify() {
        Exp simplified = ((Exp) Exp.clone(this.simplifyComponents()));

        if (((InfixExp) simplified).getLeft() != null)
            ((InfixExp) simplified).setLeft(((InfixExp) simplified).left
                    .simplify());
        else
            ((InfixExp) simplified).setLeft(getTrueVarExp(myMathType
                    .getTypeGraph()));

        if (((InfixExp) simplified).getRight() != null)
            ((InfixExp) simplified).setRight(((InfixExp) simplified).right
                    .simplify());
        else
            ((InfixExp) simplified).setLeft(getTrueVarExp(myMathType
                    .getTypeGraph()));

        // Simplify A -> true to true
        if (((InfixExp) simplified).opName.equals("implies")
                && isTrueExp(((InfixExp) simplified).getRight())) {
            return getTrueVarExp(myMathType.getTypeGraph());
        }

        if (((InfixExp) simplified).getOpName().equals("implies")
                && ((InfixExp) simplified).getRight() instanceof InfixExp) {
            // Simplify A -> B -> C to (A ^ B) -> C
            if (((InfixExp) ((InfixExp) simplified).getRight()).getOpName()
                    .toString().equals("implies")) {
                ((InfixExp) simplified).setLeft(getMathType().getTypeGraph()
                        .formConjunct(
                                ((InfixExp) simplified).getLeft(),
                                ((InfixExp) ((InfixExp) simplified).getRight())
                                        .getLeft()));
                ((InfixExp) simplified)
                        .setRight(((InfixExp) ((InfixExp) simplified)
                                .getRight()).getRight());
            }
        }

        if (((InfixExp) simplified).getOpName().equals("implies")
                && ((InfixExp) simplified).getRight() instanceof InfixExp) {
            // I need to generalize this
            if (((InfixExp) ((InfixExp) simplified).getRight()).getOpName()
                    .toString().equals("and")) {
                // Simplify A -> A ^ B to A -> B
                if (((InfixExp) simplified).getLeft().equals(
                        ((InfixExp) ((InfixExp) simplified).getRight())
                                .getLeft())) {
                    ((InfixExp) simplified)
                            .setRight(((InfixExp) ((InfixExp) simplified)
                                    .getRight()).getRight());
                    ((InfixExp) simplified).simplify();

                }
                // Simplify A -> B ^ A to A -> B
                else if (((InfixExp) simplified).getLeft().equals(
                        ((InfixExp) ((InfixExp) simplified).getRight())
                                .getRight())) {
                    ((InfixExp) simplified)
                            .setRight(((InfixExp) ((InfixExp) simplified)
                                    .getRight()).getLeft());
                    ((InfixExp) simplified).simplify();
                }

            }
        }

        if (((InfixExp) simplified).getOpName().equals("implies")
                && ((InfixExp) simplified).getLeft() instanceof InfixExp
                && ((InfixExp) simplified).getRight() instanceof InfixExp) {

            if (((InfixExp) ((InfixExp) simplified).getLeft()).onlyAndExps()
                    && ((InfixExp) ((InfixExp) simplified).getRight())
                            .onlyAndExps()) {
                List<Exp> lst =
                        ((InfixExp) ((InfixExp) simplified).getLeft())
                                .getExpressions();
                Iterator<Exp> iter = lst.iterator();
                while (iter.hasNext())
                    ((InfixExp) simplified).setRight(((InfixExp) simplified)
                            .getRight().compareWithAssumptions(iter.next()));
            }
        }
        else if (((InfixExp) simplified).getOpName().equals("implies")
                && ((InfixExp) simplified).getLeft() instanceof InfixExp) {
            if (((InfixExp) ((InfixExp) simplified).getLeft()).onlyAndExps()) {
                List<Exp> lst =
                        ((InfixExp) ((InfixExp) simplified).getLeft())
                                .getExpressions();
                Iterator<Exp> iter = lst.iterator();
                while (iter.hasNext())
                    ((InfixExp) simplified).setRight(((InfixExp) simplified)
                            .getRight().compareWithAssumptions(iter.next()));
            }
        }

        //Simplify (A ^ true) to A or (true ^ A) to A
        if (((InfixExp) simplified).opName.equals("and")) {
            if (isTrueExp(((InfixExp) simplified).getLeft()))
                return ((InfixExp) simplified).getRight();
            if (isTrueExp(((InfixExp) simplified).getRight()))
                return ((InfixExp) simplified).getLeft();
        }

        if (!simplified.equals(this))
            return simplified.simplify();

        return simplified;
    }

    public Exp compareWithAssumptions(Exp exp) {
        if (this.equals(exp))
            return getTrueVarExp(myMathType.getTypeGraph());
        if (opName.toString().equals("and")) {
            this.left = left.compareWithAssumptions(exp);
            this.right = right.compareWithAssumptions(exp);
        }
        return this;
    }

    private List<Exp> getExpressions() {
        List<Exp> lst = new List<Exp>();
        if (!opName.equals("and") && !opName.equals("implies")) {
            lst.add(this);
            return lst;
        }
        if ((left instanceof InfixExp)) {
            lst.addAll(((InfixExp) left).getExpressions());
            if (right instanceof InfixExp) {
                lst.addAll(((InfixExp) right).getExpressions());
            }
            else {
                lst.add(right);
            }
        }
        else {
            lst.add(left);
            if (right instanceof InfixExp) {
                lst.addAll(((InfixExp) right).getExpressions());
            }
            else {
                lst.add(right);
            }
        }
        return lst;
    }

    private boolean onlyAndExps() {
        if ((left instanceof InfixExp)) {
            if (((InfixExp) left).onlyAndExps())
                if (right instanceof InfixExp) {
                    if (((InfixExp) right).onlyAndExps()) {
                        if (!opName.equals("implies"))
                            return true;
                    }
                }
                else {
                    if (!opName.equals("implies"))
                        return true;
                }
        }
        else {
            if (right instanceof InfixExp) {
                if (((InfixExp) right).onlyAndExps()) {
                    if (!opName.equals("implies"))
                        return true;
                }
            }
            else {
                if (!opName.equals("implies"))
                    return true;
            }

        }
        return false;
    }

    private static PosSymbol createPosSymbol(String name) {
        PosSymbol posSym = new PosSymbol();
        posSym.setSymbol(Symbol.symbol(name));
        return posSym;
    }

    private boolean isTrueExp(Exp exp) {
        if (exp instanceof VarExp) {
            if (((VarExp) exp).getName().toString().equals(
                    getTrueVarExp(myMathType.getTypeGraph()).getName()
                            .toString())) {
                ;
                return true;
            }
        }
        return false;
    }

    public Exp copy() {
        Exp retval;

        PosSymbol newOpName = opName.copy();
        Exp newLeft = Exp.copy(left);
        Exp newRight = Exp.copy(right);
        retval = new InfixExp(null, newLeft, newOpName, newRight);
        retval.setMathType(getMathType());
        retval.setMathTypeValue(getMathTypeValue());

        return retval;
    }

    public void setAllLocations(Location loc) {
        this.location = loc;
        if (left instanceof InfixExp) {
            ((InfixExp) left).setAllLocations(loc);
        }
        else {
            left.setLocation((Location) loc.clone());
        }

        if (right instanceof InfixExp) {
            ((InfixExp) right).setAllLocations(loc);
        }
        else {
            right.setLocation((Location) loc.clone());
        }
    }

    @Override
    public String getOperatorAsString() {
        return this.opName.getName();
    }

    @Override
    public PosSymbol getOperatorAsPosSymbol() {
        return opName;
    }

    @Override
    public PosSymbol getQualifier() {
        return null;
    }
}
