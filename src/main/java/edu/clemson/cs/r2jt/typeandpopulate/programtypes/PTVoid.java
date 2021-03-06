/**
 * PTVoid.java
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
package edu.clemson.cs.r2jt.typeandpopulate.programtypes;

import edu.clemson.cs.r2jt.typeandpopulate.MTType;
import edu.clemson.cs.r2jt.typeandpopulate.entry.FacilityEntry;
import java.util.Map;
import java.util.WeakHashMap;

import edu.clemson.cs.r2jt.typereasoning.TypeGraph;

public class PTVoid extends PTType {

    private static WeakHashMap<TypeGraph, PTVoid> instances =
            new WeakHashMap<TypeGraph, PTVoid>();

    public static PTVoid getInstance(TypeGraph g) {
        PTVoid result = instances.get(g);

        if (result == null) {
            result = new PTVoid(g);
            instances.put(g, result);
        }

        return result;
    }

    private PTVoid(TypeGraph g) {
        super(g);
    }

    @Override
    public MTType toMath() {
        return getTypeGraph().VOID;
    }

    @Override
    public PTType instantiateGenerics(
            Map<String, PTType> genericInstantiations,
            FacilityEntry instantiatingFacility) {
        return this;
    }

    @Override
    public boolean equals(Object o) {
        //We override this simply to show that we've given it some thought
        return super.equals(o);
    }
}
