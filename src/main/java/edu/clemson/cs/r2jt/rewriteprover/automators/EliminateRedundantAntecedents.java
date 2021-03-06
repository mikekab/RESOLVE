/**
 * EliminateRedundantAntecedents.java
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
package edu.clemson.cs.r2jt.rewriteprover.automators;

import edu.clemson.cs.r2jt.rewriteprover.absyn.PExp;
import edu.clemson.cs.r2jt.rewriteprover.model.LocalTheorem;
import edu.clemson.cs.r2jt.rewriteprover.model.PerVCProverModel;
import edu.clemson.cs.r2jt.rewriteprover.transformations.RemoveAntecedent;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/**
 *
 * @author hamptos
 */
public class EliminateRedundantAntecedents implements Automator {

    public static final EliminateRedundantAntecedents INSTANCE =
            new EliminateRedundantAntecedents();

    private EliminateRedundantAntecedents() {

    }

    @Override
    public void step(Deque<Automator> stack, PerVCProverModel model) {
        Set<PExp> seen = new HashSet<PExp>();

        LocalTheorem curTheorem;
        LocalTheorem toRemove = null;
        Iterator<LocalTheorem> localTheorems =
                model.getLocalTheoremList().iterator();
        while (toRemove == null && localTheorems.hasNext()) {
            curTheorem = localTheorems.next();

            if (seen.contains(curTheorem.getAssertion())) {
                toRemove = curTheorem;
            }

            seen.add(curTheorem.getAssertion());
        }

        if (toRemove == null) {
            stack.pop();
        }
        else {
            new RemoveAntecedent(model, toRemove).getApplications(model).next()
                    .apply(model);
        }
    }
}
