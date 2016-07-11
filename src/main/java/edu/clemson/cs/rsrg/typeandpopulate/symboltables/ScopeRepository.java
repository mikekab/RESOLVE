/**
 * ScopeRepository.java
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
package edu.clemson.cs.rsrg.typeandpopulate.symboltables;

import edu.clemson.cs.rsrg.absyn.ResolveConceptualElement;
import edu.clemson.cs.rsrg.typeandpopulate.exception.NoSuchSymbolException;
import edu.clemson.cs.rsrg.typeandpopulate.symboltables.scopes.ModuleScope;
import edu.clemson.cs.rsrg.typeandpopulate.symboltables.scopes.Scope;
import edu.clemson.cs.rsrg.typeandpopulate.typereasoning.TypeGraph;
import edu.clemson.cs.rsrg.typeandpopulate.utilities.ModuleIdentifier;

/**
 * <p>A <code>SymbolTable</code> maps {@link ResolveConceptualElement}s and
 * {@link ModuleIdentifier}s to the {@link Scope}s they introduce.</p>
 *
 * <p>Each <code>SymbolTable</code> has a {@link TypeGraph} that relates
 * the types found in the symbol table.</p>
 *
 * <p>While this base class defines no methods for mutating the symbol table,
 * concrete subclasses may provide mutation methods.  It is particularly
 * important that clients be aware the symbol table may be "under construction"
 * even as they use it.  We therefore favor vocabulary such as "open" and
 * "closed" for scopes rather than "exists", which might imply (erroneously)
 * that scopes spring into existence atomically and fully formed.</p>
 */
public abstract class ScopeRepository {

    /**
     * <p>Returns the {@link ModuleScope} associated with the given
     * {@link ModuleIdentifier}.</p>
     *
     * @param module The module identifier.
     *
     * @returns The associated module scope.
     *
     * @throws NoSuchSymbolException If no scope has been opened for the named
     *             module.
     */
    public abstract ModuleScope getModuleScope(ModuleIdentifier module)
            throws NoSuchSymbolException;

    /**
     * <p>Returns the {@link Scope} introduced and bounded by the given
     * defining element.</p>
     *
     * @param e defining element.
     *
     * @returns The associated scope.
     *
     * @throws NoSuchSymbolException If no scope has been opened for the given
     *             defining element.
     */
    public abstract Scope getScope(ResolveConceptualElement e);

    /**
     * <p>Returns the {@link TypeGraph} that relates the types found in this
     * <code>ScopeRepository</code>.</p>
     *
     * @return The <code>TypeGraph</code>.
     */
    public abstract TypeGraph getTypeGraph();
}