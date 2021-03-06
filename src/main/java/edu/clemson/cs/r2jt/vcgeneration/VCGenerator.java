/**
 * VCGenerator.java
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
package edu.clemson.cs.r2jt.vcgeneration;

/*
 * Libraries
 */
import edu.clemson.cs.r2jt.ResolveCompiler;
import edu.clemson.cs.r2jt.absyn.*;
import edu.clemson.cs.r2jt.data.*;
import edu.clemson.cs.r2jt.init.CompileEnvironment;
import edu.clemson.cs.r2jt.misc.SourceErrorException;
import edu.clemson.cs.r2jt.rewriteprover.VC;
import edu.clemson.cs.r2jt.treewalk.TreeWalker;
import edu.clemson.cs.r2jt.treewalk.TreeWalkerVisitor;
import edu.clemson.cs.r2jt.typeandpopulate.*;
import edu.clemson.cs.r2jt.typeandpopulate.entry.*;
import edu.clemson.cs.r2jt.typeandpopulate.programtypes.PTGeneric;
import edu.clemson.cs.r2jt.typeandpopulate.programtypes.PTType;
import edu.clemson.cs.r2jt.typeandpopulate.programtypes.PTVoid;
import edu.clemson.cs.r2jt.typeandpopulate.query.EntryTypeQuery;
import edu.clemson.cs.r2jt.typeandpopulate.query.NameQuery;
import edu.clemson.cs.r2jt.typereasoning.TypeGraph;
import edu.clemson.cs.r2jt.misc.Flag;
import edu.clemson.cs.r2jt.misc.FlagDependencies;
import edu.clemson.cs.r2jt.vcgeneration.treewalkers.NestedFuncWalker;
import java.io.File;
import java.util.*;
import java.util.List;

/**
 * TODO: Write a description of this module
 */
public class VCGenerator extends TreeWalkerVisitor {

    // ===========================================================
    // Global Variables
    // ===========================================================

    // Symbol table related items
    private final MathSymbolTableBuilder mySymbolTable;
    private final TypeGraph myTypeGraph;
    private final MTType BOOLEAN;
    private final MTType MTYPE;
    private MTType Z;
    private ModuleScope myCurrentModuleScope;

    // Module level global variables
    private Exp myGlobalRequiresExp;
    private Exp myGlobalConstraintExp;

    // Operation/Procedure level global variables
    private OperationEntry myCurrentOperationEntry;
    private OperationProfileEntry myCurrentOperationProfileEntry;
    private Exp myOperationDecreasingExp;

    /**
     * <p>The current assertion we are applying
     * VC rules to.</p>
     */
    private AssertiveCode myCurrentAssertiveCode;

    /**
     * <p>A map of facility instantiated types to a list of formal and actual constraints.</p>
     */
    private final Map<VarExp, FacilityFormalToActuals> myInstantiatedFacilityArgMap;

    /**
     * <p>A list that will be built up with <code>AssertiveCode</code>
     * objects, each representing a VC or group of VCs that must be
     * satisfied to verify a parsed program.</p>
     */
    private Collection<AssertiveCode> myFinalAssertiveCodeList;

    /**
     * <p>A stack that is used to keep track of the <code>AssertiveCode</code>
     * that we still need to apply proof rules to.</p>
     */
    private Stack<AssertiveCode> myIncAssertiveCodeStack;

    /**
     * <p>A stack that is used to keep track of the information that we
     * haven't printed for the <code>AssertiveCode</code>
     * that we still need to apply proof rules to.</p>
     */
    private Stack<String> myIncAssertiveCodeStackInfo;

    /**
     * <p>The current compile environment used throughout
     * the compiler.</p>
     */
    private CompileEnvironment myInstanceEnvironment;

    /**
     * <p>A map from representation types to their constraints.</p>
     */
    private final Map<VarExp, Exp> myRepresentationConstraintMap;

    /**
     * <p>A map from representation types to their conventions.</p>
     */
    private final Map<VarExp, Exp> myRepresentationConventionsMap;

    /**
     * <p>A map from representation types to their correspondence.</p>
     */
    private final Map<VarExp, Exp> myRepresentationCorrespondenceMap;

    /**
     * <p>This object creates the different VC outputs.</p>
     */
    private OutputVCs myOutputGenerator;

    /**
     * <p>This string buffer holds all the steps
     * the VC generator takes to generate VCs.</p>
     */
    private StringBuffer myVCBuffer;

    // ===========================================================
    // Flag Strings
    // ===========================================================

    private static final String FLAG_ALTSECTION_NAME = "GenerateVCs";
    private static final String FLAG_DESC_ATLVERIFY_VC = "Generate VCs.";
    private static final String FLAG_DESC_ATTPVCS_VC =
            "Generate Performance VCs";

    // ===========================================================
    // Flags
    // ===========================================================

    public static final Flag FLAG_ALTVERIFY_VC =
            new Flag(FLAG_ALTSECTION_NAME, "altVCs", FLAG_DESC_ATLVERIFY_VC);

    public static final Flag FLAG_ALTPVCS_VC =
            new Flag(FLAG_ALTSECTION_NAME, "PVCs", FLAG_DESC_ATTPVCS_VC);

    public static final void setUpFlags() {
        FlagDependencies.addImplies(FLAG_ALTPVCS_VC, FLAG_ALTVERIFY_VC);
    }

    // ===========================================================
    // Constructors
    // ===========================================================

    public VCGenerator(ScopeRepository table, final CompileEnvironment env) {
        // Symbol table items
        mySymbolTable = (MathSymbolTableBuilder) table;
        myTypeGraph = mySymbolTable.getTypeGraph();
        BOOLEAN = myTypeGraph.BOOLEAN;
        MTYPE = myTypeGraph.CLS;
        Z = null;

        // Current items
        myCurrentModuleScope = null;
        myCurrentOperationEntry = null;
        myCurrentOperationProfileEntry = null;
        myGlobalConstraintExp = null;
        myGlobalRequiresExp = null;
        myOperationDecreasingExp = null;

        // Instance Environment
        myInstanceEnvironment = env;

        // VCs + Debugging String
        myCurrentAssertiveCode = null;
        myFinalAssertiveCodeList = new LinkedList<AssertiveCode>();
        myIncAssertiveCodeStack = new Stack<AssertiveCode>();
        myIncAssertiveCodeStackInfo = new Stack<String>();
        myInstantiatedFacilityArgMap =
                new HashMap<VarExp, FacilityFormalToActuals>();
        myRepresentationConstraintMap = new HashMap<VarExp, Exp>();
        myRepresentationConventionsMap = new HashMap<VarExp, Exp>();
        myRepresentationCorrespondenceMap = new HashMap<VarExp, Exp>();
        myOutputGenerator = null;
        myVCBuffer = new StringBuffer();
    }

    // ===========================================================
    // Visitor Methods
    // ===========================================================

    // -----------------------------------------------------------
    // ConceptBodyModuleDec
    // -----------------------------------------------------------

    @Override
    public void preConceptBodyModuleDec(ConceptBodyModuleDec dec) {
        // Verbose Mode Debug Messages
        myVCBuffer.append("\n=========================");
        myVCBuffer.append(" VC Generation Details ");
        myVCBuffer.append(" =========================\n");
        myVCBuffer.append("\n Concept Realization Name:\t");
        myVCBuffer.append(dec.getName().getName());
        myVCBuffer.append("\n Concept Name:\t");
        myVCBuffer.append(dec.getConceptName().getName());
        myVCBuffer.append("\n");
        myVCBuffer.append("\n====================================");
        myVCBuffer.append("======================================\n");
        myVCBuffer.append("\n");

        // From the list of imports, obtain the global constraints
        // of the imported modules.
        myGlobalConstraintExp =
                getConstraints(dec.getLocation(), myCurrentModuleScope
                        .getImports());

        // Obtain the global type constraints from the module parameters
        Exp typeConstraints =
                getModuleTypeConstraint(dec.getLocation(), dec.getParameters());
        if (!typeConstraints.isLiteralTrue()) {
            if (myGlobalConstraintExp.isLiteralTrue()) {
                myGlobalConstraintExp = typeConstraints;
            }
            else {
                myGlobalConstraintExp =
                        myTypeGraph.formConjunct(typeConstraints,
                                myGlobalConstraintExp);
            }
        }

        // Store the global requires clause
        myGlobalRequiresExp = getRequiresClause(dec.getLocation(), dec);

        try {
            // Obtain the global requires clause from the Concept
            ConceptModuleDec conceptModuleDec =
                    (ConceptModuleDec) mySymbolTable
                            .getModuleScope(
                                    new ModuleIdentifier(dec.getConceptName()
                                            .getName())).getDefiningElement();

            Exp conceptRequires =
                    getRequiresClause(conceptModuleDec.getLocation(),
                            conceptModuleDec);
            if (!conceptRequires.isLiteralTrue()) {
                if (myGlobalRequiresExp.isLiteralTrue()) {
                    myGlobalRequiresExp = conceptRequires;
                }
                else {
                    myGlobalRequiresExp =
                            myTypeGraph.formConjunct(myGlobalRequiresExp,
                                    conceptRequires);
                }
            }

            // Obtain the global type constraints from the Concept module parameters
            Exp conceptTypeConstraints =
                    getModuleTypeConstraint(conceptModuleDec.getLocation(),
                            conceptModuleDec.getParameters());
            if (!conceptTypeConstraints.isLiteralTrue()) {
                if (myGlobalConstraintExp.isLiteralTrue()) {
                    myGlobalConstraintExp = conceptTypeConstraints;
                }
                else {
                    myGlobalConstraintExp =
                            myTypeGraph.formConjunct(conceptTypeConstraints,
                                    myGlobalConstraintExp);
                }
            }
        }
        catch (NoSuchSymbolException e) {
            System.err.println("Module " + dec.getConceptName().getName()
                    + " does not exist or is not in scope.");
            Utilities.noSuchModule(dec.getConceptName().getLocation());
        }
    }

    // -----------------------------------------------------------
    // EnhancementBodyModuleDec
    // -----------------------------------------------------------

    @Override
    public void preEnhancementBodyModuleDec(EnhancementBodyModuleDec dec) {
        // Verbose Mode Debug Messages
        myVCBuffer.append("\n=========================");
        myVCBuffer.append(" VC Generation Details ");
        myVCBuffer.append(" =========================\n");
        myVCBuffer.append("\n Enhancement Realization Name:\t");
        myVCBuffer.append(dec.getName().getName());
        myVCBuffer.append("\n Enhancement Name:\t");
        myVCBuffer.append(dec.getEnhancementName().getName());
        myVCBuffer.append("\n Concept Name:\t");
        myVCBuffer.append(dec.getConceptName().getName());
        myVCBuffer.append("\n");
        myVCBuffer.append("\n====================================");
        myVCBuffer.append("======================================\n");
        myVCBuffer.append("\n");

        // From the list of imports, obtain the global constraints
        // of the imported modules.
        myGlobalConstraintExp =
                getConstraints(dec.getLocation(), myCurrentModuleScope
                        .getImports());

        // Obtain the global type constraints from the module parameters
        Exp typeConstraints =
                getModuleTypeConstraint(dec.getLocation(), dec.getParameters());
        if (!typeConstraints.isLiteralTrue()) {
            if (myGlobalConstraintExp.isLiteralTrue()) {
                myGlobalConstraintExp = typeConstraints;
            }
            else {
                myGlobalConstraintExp =
                        myTypeGraph.formConjunct(typeConstraints,
                                myGlobalConstraintExp);
            }
        }

        // Store the global requires clause
        myGlobalRequiresExp = getRequiresClause(dec.getLocation(), dec);

        try {
            // Obtain the global requires clause from the Concept
            ConceptModuleDec conceptModuleDec =
                    (ConceptModuleDec) mySymbolTable
                            .getModuleScope(
                                    new ModuleIdentifier(dec.getConceptName()
                                            .getName())).getDefiningElement();
            Exp conceptRequires =
                    getRequiresClause(conceptModuleDec.getLocation(),
                            conceptModuleDec);
            if (!conceptRequires.isLiteralTrue()) {
                if (myGlobalRequiresExp.isLiteralTrue()) {
                    myGlobalRequiresExp = conceptRequires;
                }
                else {
                    myGlobalRequiresExp =
                            myTypeGraph.formConjunct(myGlobalRequiresExp,
                                    conceptRequires);
                }
            }

            // Obtain the global type constraints from the Concept module parameters
            Exp conceptTypeConstraints =
                    getModuleTypeConstraint(conceptModuleDec.getLocation(),
                            conceptModuleDec.getParameters());
            if (!conceptTypeConstraints.isLiteralTrue()) {
                if (myGlobalConstraintExp.isLiteralTrue()) {
                    myGlobalConstraintExp = conceptTypeConstraints;
                }
                else {
                    myGlobalConstraintExp =
                            myTypeGraph.formConjunct(conceptTypeConstraints,
                                    myGlobalConstraintExp);
                }
            }
        }
        catch (NoSuchSymbolException e) {
            System.err.println("Module " + dec.getConceptName().getName()
                    + " does not exist or is not in scope.");
            Utilities.noSuchModule(dec.getConceptName().getLocation());
        }

        try {
            // Obtain the global requires clause from the Enhancement
            EnhancementModuleDec enhancementModuleDec =
                    (EnhancementModuleDec) mySymbolTable.getModuleScope(
                            new ModuleIdentifier(dec.getEnhancementName()
                                    .getName())).getDefiningElement();
            Exp enhancementRequires =
                    getRequiresClause(enhancementModuleDec.getLocation(),
                            enhancementModuleDec);
            if (!enhancementRequires.isLiteralTrue()) {
                if (myGlobalRequiresExp.isLiteralTrue()) {
                    myGlobalRequiresExp = enhancementRequires;
                }
                else {
                    myGlobalRequiresExp =
                            myTypeGraph.formConjunct(myGlobalRequiresExp,
                                    enhancementRequires);
                }
            }

            // Obtain the global type constraints from the Concept module parameters
            Exp enhancementTypeConstraints =
                    getModuleTypeConstraint(enhancementModuleDec.getLocation(),
                            enhancementModuleDec.getParameters());
            if (!enhancementTypeConstraints.isLiteralTrue()) {
                if (myGlobalConstraintExp.isLiteralTrue()) {
                    myGlobalConstraintExp = enhancementTypeConstraints;
                }
                else {
                    myGlobalConstraintExp =
                            myTypeGraph.formConjunct(
                                    enhancementTypeConstraints,
                                    myGlobalConstraintExp);
                }
            }
        }
        catch (NoSuchSymbolException e) {
            System.err.println("Module " + dec.getEnhancementName().getName()
                    + " does not exist or is not in scope.");
            Utilities.noSuchModule(dec.getEnhancementName().getLocation());
        }
    }

    // -----------------------------------------------------------
    // FacilityDec
    // -----------------------------------------------------------

    @Override
    public void postFacilityDec(FacilityDec dec) {
        // Applies the facility declaration rule.
        // Since this is a local facility, we will need to add
        // it to our incomplete assertive code stack.
        applyFacilityDeclRule(dec, true);

        // Loop through assertive code stack
        loopAssertiveCodeStack();
    }

    // -----------------------------------------------------------
    // FacilityModuleDec
    // -----------------------------------------------------------

    @Override
    public void preFacilityModuleDec(FacilityModuleDec dec) {
        // Verbose Mode Debug Messages
        myVCBuffer.append("\n=========================");
        myVCBuffer.append(" VC Generation Details ");
        myVCBuffer.append(" =========================\n");
        myVCBuffer.append("\n Facility Name:\t");
        myVCBuffer.append(dec.getName().getName());
        myVCBuffer.append("\n");
        myVCBuffer.append("\n====================================");
        myVCBuffer.append("======================================\n");
        myVCBuffer.append("\n");

        // From the list of imports, obtain the global constraints
        // of the imported modules.
        myGlobalConstraintExp =
                getConstraints(dec.getLocation(), myCurrentModuleScope
                        .getImports());

        // Store the global requires clause
        myGlobalRequiresExp = getRequiresClause(dec.getLocation(), dec);
    }

    // -----------------------------------------------------------
    // FacilityOperationDec
    // -----------------------------------------------------------

    @Override
    public void preFacilityOperationDec(FacilityOperationDec dec) {
        // Keep the current operation dec
        List<PTType> argTypes = new LinkedList<PTType>();
        for (ParameterVarDec p : dec.getParameters()) {
            argTypes.add(p.getTy().getProgramTypeValue());
        }
        myCurrentOperationEntry =
                Utilities.searchOperation(dec.getLocation(), null, dec
                        .getName(), argTypes, myCurrentModuleScope);
        // Obtain the performance duration clause
        if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)) {
            myCurrentOperationProfileEntry =
                    Utilities.searchOperationProfile(dec.getLocation(), null,
                            dec.getName(), argTypes, myCurrentModuleScope);
        }
    }

    @Override
    public void postFacilityOperationDec(FacilityOperationDec dec) {
        // Verbose Mode Debug Messages
        myVCBuffer.append("\n=========================");
        myVCBuffer.append(" Procedure: ");
        myVCBuffer.append(dec.getName().getName());
        myVCBuffer.append(" =========================\n");

        // The current assertive code
        myCurrentAssertiveCode = new AssertiveCode(myInstanceEnvironment, dec);

        // Obtains items from the current operation
        Location loc = dec.getLocation();
        String name = dec.getName().getName();
        OperationDec opDec =
                new OperationDec(dec.getName(), dec.getParameters(), dec
                        .getReturnTy(), dec.getStateVars(), dec.getRequires(),
                        dec.getEnsures());
        boolean isLocal =
                Utilities.isLocationOperation(dec.getName().getName(),
                        myCurrentModuleScope);
        Exp requires =
                modifyRequiresClause(getRequiresClause(loc, dec), loc,
                        myCurrentAssertiveCode, opDec, isLocal);
        Exp ensures =
                modifyEnsuresClause(getEnsuresClause(loc, dec), loc, opDec,
                        isLocal);
        List<Statement> statementList = dec.getStatements();
        List<ParameterVarDec> parameterVarList = dec.getParameters();
        List<VarDec> variableList = dec.getAllVariables();
        Exp decreasing = dec.getDecreasing();
        Exp procDur = null;
        Exp varFinalDur = null;

        // NY YS
        if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)) {
            procDur = myCurrentOperationProfileEntry.getDurationClause();

            // Loop through local variables to get their finalization duration
            for (VarDec v : dec.getVariables()) {
                Exp finalVarDur =
                        Utilities.createFinalizAnyDur(v, myTypeGraph.R);

                // Create/Add the duration expression
                if (varFinalDur == null) {
                    varFinalDur = finalVarDur;
                }
                else {
                    varFinalDur =
                            new InfixExp((Location) loc.clone(), varFinalDur,
                                    Utilities.createPosSymbol("+"), finalVarDur);
                }
                varFinalDur.setMathType(myTypeGraph.R);
            }
        }

        // Apply the procedure declaration rule
        applyProcedureDeclRule(loc, name, requires, ensures, decreasing,
                procDur, varFinalDur, parameterVarList, variableList,
                statementList, isLocal);

        // Add this to our stack of to be processed assertive codes.
        myIncAssertiveCodeStack.push(myCurrentAssertiveCode);
        myIncAssertiveCodeStackInfo.push("");

        // Set the current assertive code to null
        // YS: (We the modify requires and ensures clause needs to have
        // and current assertive code to work. Not very clean way to
        // solve the problem, but should work.)
        myCurrentAssertiveCode = null;

        // Loop through assertive code stack
        loopAssertiveCodeStack();

        myOperationDecreasingExp = null;
        myCurrentOperationEntry = null;
        myCurrentOperationProfileEntry = null;
    }

    // -----------------------------------------------------------
    // ModuleDec
    // -----------------------------------------------------------

    @Override
    public void preModuleDec(ModuleDec dec) {
        // Set the current module scope
        try {
            myCurrentModuleScope =
                    mySymbolTable.getModuleScope(new ModuleIdentifier(dec));

            // Get "Z" from the TypeGraph
            Z = Utilities.getMathTypeZ(dec.getLocation(), myCurrentModuleScope);

            // Apply the facility declaration rule to imported facility declarations.
            List<SymbolTableEntry> results =
                    myCurrentModuleScope
                            .query(new EntryTypeQuery<SymbolTableEntry>(
                                    FacilityEntry.class,
                                    MathSymbolTable.ImportStrategy.IMPORT_NAMED,
                                    MathSymbolTable.FacilityStrategy.FACILITY_INSTANTIATE));
            for (SymbolTableEntry s : results) {
                if (s.getSourceModuleIdentifier().compareTo(
                        myCurrentModuleScope.getModuleIdentifier()) != 0) {
                    // Do all the facility declaration logic, but don't add this
                    // to our incomplete assertive code stack. We shouldn't need to
                    // verify facility declarations that are imported.
                    FacilityDec facDec =
                            (FacilityDec) s.toFacilityEntry(dec.getLocation())
                                    .getDefiningElement();
                    applyFacilityDeclRule(facDec, false);
                }
            }
        }
        catch (NoSuchSymbolException e) {
            System.err.println("Module " + dec.getName()
                    + " does not exist or is not in scope.");
            Utilities.noSuchModule(dec.getLocation());
        }
    }

    @Override
    public void postModuleDec(ModuleDec dec) {
        // Create the output generator and finalize output
        myOutputGenerator =
                new OutputVCs(myInstanceEnvironment, myFinalAssertiveCodeList,
                        myVCBuffer);

        // Check if it is generating VCs for WebIDE or not.
        if (myInstanceEnvironment.flags.isFlagSet(ResolveCompiler.FLAG_XML_OUT)) {
            myOutputGenerator.outputToJSON();
        }
        else {
            // Print to file if we are in debug mode
            // TODO: Add debug flag here
            String filename;
            if (myInstanceEnvironment.getOutputFilename() != null) {
                filename = myInstanceEnvironment.getOutputFilename();
            }
            else {
                filename = createVCFileName();
            }
            myOutputGenerator.outputToFile(filename);
        }

        // Set the module level global variables to null
        myCurrentModuleScope = null;
        myGlobalConstraintExp = null;
        myGlobalRequiresExp = null;
    }

    // -----------------------------------------------------------
    // ProcedureDec
    // -----------------------------------------------------------

    @Override
    public void preProcedureDec(ProcedureDec dec) {
        // Keep the current operation dec
        List<PTType> argTypes = new LinkedList<PTType>();
        for (ParameterVarDec p : dec.getParameters()) {
            argTypes.add(p.getTy().getProgramTypeValue());
        }
        myCurrentOperationEntry =
                Utilities.searchOperation(dec.getLocation(), null, dec
                        .getName(), argTypes, myCurrentModuleScope);
        // Obtain the performance duration clause
        if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)) {
            myCurrentOperationProfileEntry =
                    Utilities.searchOperationProfile(dec.getLocation(), null,
                            dec.getName(), argTypes, myCurrentModuleScope);
        }
    }

    @Override
    public void postProcedureDec(ProcedureDec dec) {
        // Verbose Mode Debug Messages
        myVCBuffer.append("\n=========================");
        myVCBuffer.append(" Procedure: ");
        myVCBuffer.append(dec.getName().getName());
        myVCBuffer.append(" =========================\n");

        // The current assertive code
        myCurrentAssertiveCode = new AssertiveCode(myInstanceEnvironment, dec);

        // Obtains items from the current operation
        OperationDec opDec =
                (OperationDec) myCurrentOperationEntry.getDefiningElement();
        Location loc = dec.getLocation();
        String name = dec.getName().getName();
        boolean isLocal =
                Utilities.isLocationOperation(dec.getName().getName(),
                        myCurrentModuleScope);
        Exp requires =
                modifyRequiresClause(getRequiresClause(loc, opDec), loc,
                        myCurrentAssertiveCode, opDec, isLocal);
        Exp ensures =
                modifyEnsuresClause(getEnsuresClause(loc, opDec), loc, opDec,
                        isLocal);
        List<Statement> statementList = dec.getStatements();
        List<ParameterVarDec> parameterVarList = dec.getParameters();
        List<VarDec> variableList = dec.getAllVariables();
        Exp decreasing = dec.getDecreasing();
        Exp procDur = null;
        Exp varFinalDur = null;

        // NY YS
        if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)) {
            procDur = myCurrentOperationProfileEntry.getDurationClause();

            // Loop through local variables to get their finalization duration
            for (VarDec v : dec.getVariables()) {
                Exp finalVarDur = Utilities.createFinalizAnyDur(v, BOOLEAN);

                // Create/Add the duration expression
                if (varFinalDur == null) {
                    varFinalDur = finalVarDur;
                }
                else {
                    varFinalDur =
                            new InfixExp((Location) loc.clone(), varFinalDur,
                                    Utilities.createPosSymbol("+"), finalVarDur);
                }
                varFinalDur.setMathType(myTypeGraph.R);
            }
        }

        // Apply the procedure declaration rule
        applyProcedureDeclRule(loc, name, requires, ensures, decreasing,
                procDur, varFinalDur, parameterVarList, variableList,
                statementList, isLocal);

        // Add this to our stack of to be processed assertive codes.
        myIncAssertiveCodeStack.push(myCurrentAssertiveCode);
        myIncAssertiveCodeStackInfo.push("");

        // Set the current assertive code to null
        // YS: (We the modify requires and ensures clause needs to have
        // and current assertive code to work. Not very clean way to
        // solve the problem, but should work.)
        myCurrentAssertiveCode = null;

        // Loop through assertive code stack
        loopAssertiveCodeStack();

        myOperationDecreasingExp = null;
        myCurrentOperationEntry = null;
        myCurrentOperationProfileEntry = null;
    }

    // -----------------------------------------------------------
    // RepresentationDec
    // -----------------------------------------------------------

    @Override
    public void postRepresentationDec(RepresentationDec dec) {
        // Applies the initialization rule
        applyInitializationRule(dec);

        // Applies the correspondence rule
        applyCorrespondenceRule(dec);

        // Loop through assertive code stack
        loopAssertiveCodeStack();
    }

    // ===========================================================
    // Public Methods
    // ===========================================================

    // -----------------------------------------------------------
    // Prover Mode
    // -----------------------------------------------------------

    /**
     * <p>The set of immmutable VCs that the in house provers can use.</p>
     *
     * @return VCs to be proved.
     */
    public List<VC> proverOutput() {
        return myOutputGenerator.getProverOutput();
    }

    // ===========================================================
    // Private Methods
    // ===========================================================

    /**
     * <p>Loop through the list of <code>VarDec</code>, search
     * for their corresponding <code>ProgramVariableEntry</code>
     * and add the result to the list of free variables.</p>
     *
     * @param variableList List of the all variables as
     *                     <code>VarDec</code>.
     */
    private void addVarDecsAsFreeVars(List<VarDec> variableList) {
        // Loop through the variable list
        for (VarDec v : variableList) {
            myCurrentAssertiveCode.addFreeVar(Utilities.createVarExp(v
                    .getLocation(), null, v.getName(), v.getTy()
                    .getMathTypeValue(), null));
        }
    }

    /**
     * <p>Converts each actual programming expression into their mathematical
     * counterparts. It is possible that the passed in programming expression
     * contains nested function calls, therefore we will need to obtain all the
     * requires clauses from the different calls and add it as a confirm statement
     * in our current assertive code.</p>
     *
     * @param assertiveCode Current assertive code.
     * @param actualParams The list of actual parameter arguments.
     *
     * @return A list containing the newly created mathematical expression.
     */
    private List<Exp> createModuleActualArgExpList(AssertiveCode assertiveCode,
            List<ModuleArgumentItem> actualParams) {
        List<Exp> retExpList = new ArrayList<Exp>();

        for (ModuleArgumentItem item : actualParams) {
            // Obtain the math type for the module argument item
            MTType type;
            if (item.getProgramTypeValue() != null
                    && !(item.getProgramTypeValue() instanceof PTVoid)) {
                type = item.getProgramTypeValue().toMath();
            }
            else {
                type = item.getMathType();
            }

            // Convert the module argument items into math expressions
            Exp expToUse;
            if (item.getName() != null) {
                expToUse =
                        Utilities.createVarExp(item.getLocation(), item
                                .getQualifier(), item.getName(), type, null);
            }
            else {
                // Check for nested function calls in ProgramDotExp
                // and ProgramParamExp.
                ProgramExp p = item.getEvalExp();
                if (p instanceof ProgramDotExp || p instanceof ProgramParamExp) {
                    NestedFuncWalker nfw =
                            new NestedFuncWalker(null, null, mySymbolTable,
                                    myCurrentModuleScope, assertiveCode,
                                    myInstantiatedFacilityArgMap);
                    TreeWalker tw = new TreeWalker(nfw);
                    tw.visit(p);

                    // Add the requires clause as something we need to confirm
                    Exp pRequires = nfw.getRequiresClause();
                    if (!pRequires.isLiteralTrue()) {
                        assertiveCode.addConfirm(pRequires.getLocation(),
                                pRequires, false);
                    }

                    // Use the modified ensures clause as the new expression we want
                    // to replace.
                    expToUse = nfw.getEnsuresClause();
                }
                // For all other types of arguments, simply convert it to a
                // math expression.
                else {
                    expToUse = Utilities.convertExp(p, myCurrentModuleScope);
                }
            }

            // Add this to our return list
            retExpList.add(expToUse);
        }

        return retExpList;
    }

    /**
     * <p>Converts each module's formal argument into variable expressions. This is only
     * possible if the argument is of type <code>ConstantParamDec</code>. All other types
     * are simply ignored and has mapped value of <code>null</code>.</p>
     *
     * @param formalParams The formal parameter list for a <code>ModuleDec</code>.
     *
     * @return A list containing the newly created variable expression.
     */
    private List<Exp> createModuleFormalArgExpList(
            List<ModuleParameterDec> formalParams) {
        List<Exp> retExpList = new ArrayList<Exp>();

        // Create a variable expression for each of the module arguments
        // and put it in our map.
        for (ModuleParameterDec dec : formalParams) {
            Dec wrappedDec = dec.getWrappedDec();

            // Only do this for constant parameter and operation declarations
            // We don't really care about type declarations or definitions.
            Exp newExp;
            if (wrappedDec instanceof ConstantParamDec
                    || wrappedDec instanceof ConceptTypeParamDec) {
                newExp =
                        Utilities.createVarExp(wrappedDec.getLocation(), null,
                                wrappedDec.getName(), wrappedDec.getMathType(),
                                null);
            }
            else if (wrappedDec instanceof OperationDec) {
                OperationDec opDec = (OperationDec) wrappedDec;
                newExp =
                        Utilities.createVarExp(wrappedDec.getLocation(), null,
                                opDec.getName(), dec.getMathType(), null);
            }
            else {
                newExp = null;
            }

            // Store the result
            retExpList.add(newExp);
        }

        return retExpList;
    }

    /**
     * <p>Creates the name of the output file.</p>
     *
     * @return Name of the file
     */
    private String createVCFileName() {
        File file = myInstanceEnvironment.getTargetFile();
        ModuleID cid = myInstanceEnvironment.getModuleID(file);
        file = myInstanceEnvironment.getFile(cid);
        String filename = file.toString();
        int temp = filename.indexOf(".");
        String tempfile = filename.substring(0, temp);
        String mainFileName;

        mainFileName = tempfile + ".asrt_new";

        return mainFileName;
    }

    /**
     * <p>This is a helper method that checks to see if the given assume expression
     * can be used to prove our confirm expression. This is done by finding the
     * intersection between the set of symbols in the assume expression and
     * the set of symbols in the confirm expression.</p>
     *
     * <p>If the assume expressions are part of a stipulate assume clause,
     * then we keep all the assume expressions no matter what.</p>
     *
     * <p>If it is not a stipulate assume clause, we loop though keep looping through
     * all the assume expressions until we can't form another implies.</p>
     *
     * @param confirmExp The current confirm expression.
     * @param remAssumeExpList The list of remaining assume expressions.
     * @param isStipulate Whether or not the assume expression is an stipulate assume expression.
     *
     * @return The modified confirm expression.
     */
    private Exp formImplies(Exp confirmExp, List<Exp> remAssumeExpList,
            boolean isStipulate) {
        // If it is stipulate clause, keep it no matter what
        if (isStipulate) {
            for (Exp assumeExp : remAssumeExpList) {
                confirmExp =
                        myTypeGraph.formImplies(Exp.copy(assumeExp), Exp
                                .copy(confirmExp));
            }
        }
        else {
            boolean checkList = false;
            if (remAssumeExpList.size() > 0) {
                checkList = true;
            }

            // Loop until we no longer add more expressions or we have added all
            // expressions in the remaining assume expression list.
            while (checkList) {
                List<Exp> tmpExpList = new ArrayList<Exp>();
                boolean formedImplies = false;

                for (Exp assumeExp : remAssumeExpList) {
                    // Create a new implies expression if there are common symbols
                    // in the assume and in the confirm. (Parsimonious step)
                    Set<String> intersection = Utilities.getSymbols(confirmExp);
                    intersection.retainAll(Utilities.getSymbols(assumeExp));

                    if (!intersection.isEmpty()) {
                        // Don't form implies if we have "Assume true"
                        if (!assumeExp.isLiteralTrue()) {
                            confirmExp =
                                    myTypeGraph.formImplies(
                                            Exp.copy(assumeExp), Exp
                                                    .copy(confirmExp));
                            formedImplies = true;
                        }
                    }
                    else {
                        // Form implies if we have "Assume false"
                        if (assumeExp.isLiteralFalse()) {
                            confirmExp =
                                    myTypeGraph.formImplies(
                                            Exp.copy(assumeExp), Exp
                                                    .copy(confirmExp));
                            formedImplies = true;
                        }
                        else {
                            tmpExpList.add(assumeExp);
                        }
                    }
                }

                remAssumeExpList = tmpExpList;
                if (remAssumeExpList.size() > 0) {
                    // Check to see if we formed an implication
                    if (formedImplies) {
                        // Loop again to see if we can form any more implications
                        checkList = true;
                    }
                    else {
                        // If no implications are formed, then none of the remaining
                        // expressions will be helpful.
                        checkList = false;
                    }
                }
                else {
                    // Since we are done with all assume expressions, we can quit
                    // out of the loop.
                    checkList = false;
                }
            }
        }

        return confirmExp;
    }

    /**
     * <p>A helper method to deal with operations as parameters.</p>
     *
     * @param loc Location of some facility declaration.
     * @param assertiveCode The current assertive code.
     * @param formalParams The formal parameters.
     * @param actualParams The actual parameters.
     * @param conceptFormalParamExp The concept formal parameter expression.
     * @param conceptActualParamExp The concept actual parameter expression.
     * @param conceptRealizFormalParamExp The concept realization formal parameter expression.
     * @param conceptRealizActualParamExp The concept realization actual parameter expression.
     * @param enhancementFormalParamExp The enhancement formal parameter expression.
     * @param enhancementActualParamExp The enhancement actual parameter expression.
     * @param enhancementRealizFormalParamExp The enhancement realization formal parameter expression.
     * @param enhancementRealizActualParamExp The enhancement realization actual parameter expression.
     * @return
     */
    private AssertiveCode facilityDeclOperationParamHelper(Location loc,
            AssertiveCode assertiveCode, List<ModuleParameterDec> formalParams,
            List<ModuleArgumentItem> actualParams,
            List<Exp> conceptFormalParamExp, List<Exp> conceptActualParamExp,
            List<Exp> conceptRealizFormalParamExp,
            List<Exp> conceptRealizActualParamExp,
            List<Exp> enhancementFormalParamExp,
            List<Exp> enhancementActualParamExp,
            List<Exp> enhancementRealizFormalParamExp,
            List<Exp> enhancementRealizActualParamExp) {
        AssertiveCode copyAssertiveCode = new AssertiveCode(assertiveCode);

        Iterator<ModuleParameterDec> realizParameterIt =
                formalParams.iterator();
        Iterator<ModuleArgumentItem> realizArgumentItemIt =
                actualParams.iterator();
        while (realizParameterIt.hasNext() && realizArgumentItemIt.hasNext()) {
            ModuleParameterDec moduleParameterDec = realizParameterIt.next();
            ModuleArgumentItem moduleArgumentItem = realizArgumentItemIt.next();

            if (moduleParameterDec.getWrappedDec() instanceof OperationDec) {
                // Formal operation
                OperationDec formalOperationDec =
                        (OperationDec) moduleParameterDec.getWrappedDec();
                boolean isFormalOpDecLocal =
                        Utilities.isLocationOperation(formalOperationDec
                                .getName().getName(), myCurrentModuleScope);
                Exp formalOperationRequires =
                        getRequiresClause(formalOperationDec.getLocation(),
                                formalOperationDec);
                Exp formalOperationEnsures =
                        getEnsuresClause(formalOperationDec.getLocation(),
                                formalOperationDec);

                // Construct a list of formal parameters as expressions
                // for substitution purposes.
                List<ParameterVarDec> formalParameterVarDecs =
                        formalOperationDec.getParameters();
                List<Exp> formalParamAsExp = new ArrayList<Exp>();
                for (ParameterVarDec varDec : formalParameterVarDecs) {
                    Ty varDecTy = varDec.getTy();

                    // varDec as VarExp
                    VarExp varDecExp =
                            Utilities.createVarExp(varDec.getLocation(), null,
                                    varDec.getName(), varDecTy.getMathType(),
                                    null);
                    formalParamAsExp.add(varDecExp);

                    // #varDec as OldExp
                    OldExp oldVarDecExp =
                            new OldExp(varDec.getLocation(), Exp
                                    .copy(varDecExp));
                    formalParamAsExp.add(oldVarDecExp);
                }

                if (formalOperationDec.getReturnTy() != null) {
                    Ty varDecTy = formalOperationDec.getReturnTy();
                    formalParamAsExp.add(Utilities.createVarExp(varDecTy
                            .getLocation(), null, formalOperationDec.getName(),
                            varDecTy.getMathType(), null));
                }

                // Locate the corresponding actual operation
                OperationDec actualOperationDec = null;
                List<Exp> actualParamAsExp = new ArrayList<Exp>();
                try {
                    OperationEntry op =
                            myCurrentModuleScope
                                    .queryForOne(
                                            new NameQuery(
                                                    moduleArgumentItem
                                                            .getQualifier(),
                                                    moduleArgumentItem
                                                            .getName(),
                                                    MathSymbolTable.ImportStrategy.IMPORT_NAMED,
                                                    MathSymbolTable.FacilityStrategy.FACILITY_INSTANTIATE,
                                                    true))
                                    .toOperationEntry(loc);

                    if (op.getDefiningElement() instanceof OperationDec) {
                        actualOperationDec =
                                (OperationDec) op.getDefiningElement();
                    }
                    else {
                        FacilityOperationDec fOpDec =
                                (FacilityOperationDec) op.getDefiningElement();
                        actualOperationDec =
                                new OperationDec(fOpDec.getName(), fOpDec
                                        .getParameters(), fOpDec.getReturnTy(),
                                        fOpDec.getStateVars(), fOpDec
                                                .getRequires(), fOpDec
                                                .getEnsures());
                    }

                    // Construct a list of actual parameters as expressions
                    // for substitution purposes.
                    List<ParameterVarDec> parameterVarDecs =
                            actualOperationDec.getParameters();
                    for (ParameterVarDec varDec : parameterVarDecs) {
                        Ty varDecTy = varDec.getTy();

                        // varDec as VarExp
                        VarExp varDecExp =
                                Utilities.createVarExp(varDec.getLocation(),
                                        null, varDec.getName(), varDecTy
                                                .getMathType(), null);
                        actualParamAsExp.add(varDecExp);

                        // #varDec as OldExp
                        OldExp oldVarDecExp =
                                new OldExp(varDec.getLocation(), Exp
                                        .copy(varDecExp));
                        actualParamAsExp.add(oldVarDecExp);
                    }

                    // TODO: Move this to the populator
                    opAsParameterSanityCheck(moduleArgumentItem.getLocation(),
                            formalParameterVarDecs, parameterVarDecs);

                    // Add any return types as something we need to replace
                    if (actualOperationDec.getReturnTy() != null) {
                        Ty varDecTy = actualOperationDec.getReturnTy();
                        actualParamAsExp.add(Utilities.createVarExp(varDecTy
                                .getLocation(), null, actualOperationDec
                                .getName(), varDecTy.getMathType(), null));
                    }
                }
                catch (NoSuchSymbolException nsse) {
                    Utilities.noSuchSymbol(moduleArgumentItem.getQualifier(),
                            moduleArgumentItem.getName().getName(), loc);
                }
                catch (DuplicateSymbolException dse) {
                    //This should be caught earlier, when the duplicate operation is
                    //created
                    throw new RuntimeException(dse);
                }
                Exp actualOperationRequires =
                        getRequiresClause(moduleArgumentItem.getLocation(),
                                actualOperationDec);
                Exp actualOperationEnsures =
                        getEnsuresClause(moduleArgumentItem.getLocation(),
                                actualOperationDec);

                // Add in the qualifier if there is one in the module argument
                if (moduleArgumentItem.getQualifier() != null) {
                    VarExp notQualifiedOp =
                            Utilities.createVarExp(moduleArgumentItem
                                    .getLocation(), null, moduleArgumentItem
                                    .getName(), moduleArgumentItem
                                    .getMathType(), null);
                    VarExp qualifiedOp =
                            Utilities.createVarExp(moduleArgumentItem
                                    .getLocation(), moduleArgumentItem
                                    .getQualifier(), moduleArgumentItem
                                    .getName(), moduleArgumentItem
                                    .getMathType(), null);

                    actualOperationRequires =
                            Utilities.replace(actualOperationRequires,
                                    notQualifiedOp, qualifiedOp);
                    actualOperationEnsures =
                            Utilities.replace(actualOperationEnsures,
                                    notQualifiedOp, qualifiedOp);
                }

                // Facility Decl Rule (Operations as Parameters):
                // preRP [ rn ~> rn_exp, rx ~> irx ] implies preIRP
                Exp formalRequires =
                        modifyRequiresClause(formalOperationRequires,
                                moduleParameterDec.getLocation(),
                                copyAssertiveCode, formalOperationDec,
                                isFormalOpDecLocal);
                formalRequires =
                        replaceFacilityDeclarationVariables(formalRequires,
                                conceptFormalParamExp, conceptActualParamExp);
                formalRequires =
                        replaceFacilityDeclarationVariables(formalRequires,
                                conceptRealizFormalParamExp,
                                conceptRealizActualParamExp);
                formalRequires =
                        replaceFacilityDeclarationVariables(formalRequires,
                                enhancementFormalParamExp,
                                enhancementActualParamExp);
                formalRequires =
                        replaceFacilityDeclarationVariables(formalRequires,
                                enhancementRealizFormalParamExp,
                                enhancementRealizActualParamExp);
                formalRequires =
                        replaceFacilityDeclarationVariables(formalRequires,
                                formalParamAsExp, actualParamAsExp);

                if (!actualOperationRequires
                        .equals(myTypeGraph.getTrueVarExp())) {
                    Location newLoc =
                            (Location) actualOperationRequires.getLocation()
                                    .clone();
                    newLoc.setDetails("Requires Clause of "
                            + formalOperationDec.getName().getName()
                            + " implies the Requires Clause of "
                            + actualOperationDec.getName().getName()
                            + " in Facility Instantiation Rule");

                    Exp newConfirmExp;
                    if (!formalRequires.equals(myTypeGraph.getTrueVarExp())) {
                        newConfirmExp =
                                myTypeGraph.formImplies(formalRequires,
                                        actualOperationRequires);
                    }
                    else {
                        newConfirmExp = actualOperationRequires;
                    }
                    Utilities.setLocation(newConfirmExp, newLoc);
                    copyAssertiveCode.addConfirm(newLoc, newConfirmExp, false);
                }

                // Facility Decl Rule (Operations as Parameters):
                // postIRP implies postRP [ rn ~> rn_exp, #rx ~> #irx, rx ~> irx ]
                Exp formalEnsures =
                        modifyEnsuresClause(formalOperationEnsures,
                                moduleParameterDec.getLocation(),
                                formalOperationDec, isFormalOpDecLocal);
                formalEnsures =
                        replaceFacilityDeclarationVariables(formalEnsures,
                                conceptFormalParamExp, conceptActualParamExp);
                formalEnsures =
                        replaceFacilityDeclarationVariables(formalEnsures,
                                conceptRealizFormalParamExp,
                                conceptRealizActualParamExp);
                formalEnsures =
                        replaceFacilityDeclarationVariables(formalEnsures,
                                enhancementFormalParamExp,
                                enhancementActualParamExp);
                formalEnsures =
                        replaceFacilityDeclarationVariables(formalEnsures,
                                enhancementRealizFormalParamExp,
                                enhancementRealizActualParamExp);
                formalEnsures =
                        replaceFacilityDeclarationVariables(formalEnsures,
                                formalParamAsExp, actualParamAsExp);

                if (!formalEnsures.equals(myTypeGraph.getTrueVarExp())) {
                    Location newLoc =
                            (Location) actualOperationEnsures.getLocation()
                                    .clone();

                    // Add qualification to the name (if needed)
                    String actualOpName =
                            actualOperationDec.getName().getName();
                    if (moduleArgumentItem.getQualifier() != null) {
                        actualOpName =
                                moduleArgumentItem.getQualifier().getName()
                                        + "." + actualOpName;
                    }

                    newLoc.setDetails("Ensures Clause of " + actualOpName
                            + " implies the Ensures Clause of "
                            + formalOperationDec.getName().getName()
                            + " in Facility Instantiation Rule");

                    Exp newConfirmExp;
                    if (!actualOperationEnsures.equals(myTypeGraph
                            .getTrueVarExp())) {
                        newConfirmExp =
                                myTypeGraph.formImplies(actualOperationEnsures,
                                        formalEnsures);
                    }
                    else {
                        newConfirmExp = formalEnsures;
                    }
                    Utilities.setLocation(newConfirmExp, newLoc);
                    copyAssertiveCode.addConfirm(newLoc, newConfirmExp, false);
                }
            }
        }

        return copyAssertiveCode;
    }

    /**
     * <p>This method iterates through each of the assume expressions.
     * If the expression is a replaceable equals expression, it will substitute
     * all instances of the expression in the rest of the assume expression
     * list and in the confirm expression list.</p>
     *
     * <p>When it is not a replaceable expression, we apply a step to generate
     * parsimonious VCs.</p>
     *
     * @param confirmExpList The list of conjunct confirm expressions.
     * @param assumeExpList The list of conjunct assume expressions.
     * @param isStipulate Boolean to indicate whether it is a stipulate assume
     *                    clause and we need to keep the assume statement.
     *
     * @return The modified confirm statement expression in <code>Exp/code> form.
     */
    private Exp formParsimoniousVC(List<Exp> confirmExpList,
            List<Exp> assumeExpList, boolean isStipulate) {
        // Loop through each confirm expression
        for (int i = 0; i < confirmExpList.size(); i++) {
            Exp currentConfirmExp = confirmExpList.get(i);

            // Make a deep copy of the assume expression list
            List<Exp> assumeExpCopyList = new ArrayList<Exp>();
            for (Exp assumeExp : assumeExpList) {
                assumeExpCopyList.add(Exp.copy(assumeExp));
            }

            // Stores the remaining assume expressions
            // we have not substituted. Note that if the expression
            // is part of a stipulate assume statement, we keep
            // the assume no matter what.
            List<Exp> remAssumeExpList = new ArrayList<Exp>();

            // Loop through each assume expression
            for (int j = 0; j < assumeExpCopyList.size(); j++) {
                Exp currentAssumeExp = assumeExpCopyList.get(j);
                Exp tmp;
                boolean hasVerificationVar = false;
                boolean isConceptualVar = false;
                boolean doneReplacement = false;

                // Attempts to simplify equality expressions
                if (currentAssumeExp instanceof EqualsExp
                        && ((EqualsExp) currentAssumeExp).getOperator() == EqualsExp.EQUAL) {
                    EqualsExp equalsExp = (EqualsExp) currentAssumeExp;
                    boolean isLeftReplaceable =
                            Utilities.containsReplaceableExp(equalsExp
                                    .getLeft());
                    boolean isRightReplaceable =
                            Utilities.containsReplaceableExp(equalsExp
                                    .getRight());

                    // Check to see if we have P_val or Cum_Dur
                    if (equalsExp.getLeft() instanceof VarExp) {
                        if (((VarExp) equalsExp.getLeft()).getName().getName()
                                .matches("\\?*P_val")
                                || ((VarExp) equalsExp.getLeft()).getName()
                                        .getName().matches("\\?*Cum_Dur")) {
                            hasVerificationVar = true;
                        }
                    }
                    // Check to see if we have Conc.[expression]
                    else if (equalsExp.getLeft() instanceof DotExp) {
                        DotExp tempLeft = (DotExp) equalsExp.getLeft();
                        isConceptualVar = tempLeft.containsVar("Conc", false);
                    }

                    // Check if both the left and right are replaceable
                    if (isLeftReplaceable && isRightReplaceable) {
                        // Only check for verification variable on the left
                        // hand side. If that is the case, we know the
                        // right hand side is the only one that makes sense
                        // in the current context, therefore we do the
                        // substitution.
                        if (hasVerificationVar || isConceptualVar) {
                            tmp =
                                    Utilities.replace(currentConfirmExp,
                                            equalsExp.getLeft(), equalsExp
                                                    .getRight());

                            // Check to see if something has been replaced
                            if (!tmp.equals(currentConfirmExp)) {
                                // Replace all instances of the left side in
                                // the assume expressions we have already processed.
                                for (int k = 0; k < remAssumeExpList.size(); k++) {
                                    Exp newAssumeExp =
                                            Utilities.replace(remAssumeExpList
                                                    .get(k), equalsExp
                                                    .getLeft(), equalsExp
                                                    .getRight());
                                    remAssumeExpList.set(k, newAssumeExp);
                                }

                                // Replace all instances of the left side in
                                // the assume expressions we haven't processed.
                                for (int k = j + 1; k < assumeExpCopyList
                                        .size(); k++) {
                                    Exp newAssumeExp =
                                            Utilities.replace(assumeExpCopyList
                                                    .get(k), equalsExp
                                                    .getLeft(), equalsExp
                                                    .getRight());
                                    assumeExpCopyList.set(k, newAssumeExp);
                                }

                                doneReplacement = true;
                            }
                        }
                        else {
                            // Don't do any substitutions, we don't know
                            // which makes sense in the current context.
                            tmp = currentConfirmExp;
                        }
                    }
                    // Check if left hand side is replaceable
                    else if (isLeftReplaceable) {
                        // Create a temp expression where left is replaced with the right
                        tmp =
                                Utilities.replace(currentConfirmExp, equalsExp
                                        .getLeft(), equalsExp.getRight());

                        // Check to see if something has been replaced
                        if (!tmp.equals(currentConfirmExp)) {
                            doneReplacement = true;
                        }

                        // Replace all instances of the left side in
                        // the assume expressions we have already processed.
                        for (int k = 0; k < remAssumeExpList.size(); k++) {
                            Exp newAssumeExp =
                                    Utilities.replace(remAssumeExpList.get(k),
                                            equalsExp.getLeft(), equalsExp
                                                    .getRight());
                            remAssumeExpList.set(k, newAssumeExp);
                        }

                        // Replace all instances of the left side in
                        // the assume expressions we haven't processed.
                        for (int k = j + 1; k < assumeExpCopyList.size(); k++) {
                            Exp newAssumeExp =
                                    Utilities.replace(assumeExpCopyList.get(k),
                                            equalsExp.getLeft(), equalsExp
                                                    .getRight());
                            assumeExpCopyList.set(k, newAssumeExp);
                        }
                    }
                    // Only right hand side is replaceable
                    else if (isRightReplaceable) {
                        // Create a temp expression where right is replaced with the left
                        tmp =
                                Utilities.replace(currentConfirmExp, equalsExp
                                        .getRight(), equalsExp.getLeft());

                        // Check to see if something has been replaced
                        if (!tmp.equals(currentConfirmExp)) {
                            doneReplacement = true;
                        }

                        // Replace all instances of the right side in
                        // the assume expressions we have already processed.
                        for (int k = 0; k < remAssumeExpList.size(); k++) {
                            Exp newAssumeExp =
                                    Utilities.replace(remAssumeExpList.get(k),
                                            equalsExp.getRight(), equalsExp
                                                    .getLeft());
                            remAssumeExpList.set(k, newAssumeExp);
                        }

                        // Replace all instances of the right side in
                        // the assume expressions we haven't processed.
                        for (int k = j + 1; k < assumeExpCopyList.size(); k++) {
                            Exp newAssumeExp =
                                    Utilities.replace(assumeExpCopyList.get(k),
                                            equalsExp.getRight(), equalsExp
                                                    .getLeft());
                            assumeExpCopyList.set(k, newAssumeExp);
                        }
                    }
                    // Both sides are not replaceable
                    else {
                        tmp = currentConfirmExp;
                    }
                }
                else {
                    tmp = currentConfirmExp;
                }

                // Check to see if this is a stipulate assume clause
                // If yes, we keep a copy of the current
                // assume expression.
                if (isStipulate) {
                    remAssumeExpList.add(Exp.copy(currentAssumeExp));
                }
                else {
                    // Update the current confirm expression
                    // if we did a replacement.
                    if (doneReplacement) {
                        currentConfirmExp = tmp;
                    }
                    else {
                        // Check to see if this a verification
                        // variable. If yes, we don't keep this assume.
                        // Otherwise, we need to store this for the
                        // step that generates the parsimonious vcs.
                        if (!hasVerificationVar) {
                            remAssumeExpList.add(Exp.copy(currentAssumeExp));
                        }
                    }
                }
            }

            // Use the remaining assume expression list
            // Create a new implies expression if there are common symbols
            // in the assume and in the confirm. (Parsimonious step)
            Exp newConfirmExp =
                    formImplies(currentConfirmExp, remAssumeExpList,
                            isStipulate);
            confirmExpList.set(i, newConfirmExp);
        }

        // Form the return confirm statement
        Exp retExp = myTypeGraph.getTrueVarExp();
        for (Exp e : confirmExpList) {
            if (retExp.isLiteralTrue()) {
                retExp = e;
            }
            else {
                retExp = myTypeGraph.formConjunct(retExp, e);
            }
        }

        return retExp;
    }

    /**
     * <p>Returns all the constraint clauses combined together for the
     * for the current <code>ModuleDec</code>.</p>
     *
     * @param loc The location of the <code>ModuleDec</code>.
     * @param imports The list of imported modules.
     *
     * @return The constraint clause <code>Exp</code>.
     */
    private Exp getConstraints(Location loc, List<ModuleIdentifier> imports) {
        Exp retExp = null;
        List<String> importedConceptName = new LinkedList<String>();

        // Loop
        for (ModuleIdentifier mi : imports) {
            try {
                ModuleDec dec =
                        mySymbolTable.getModuleScope(mi).getDefiningElement();
                List<Exp> contraintExpList = null;

                // Handling for facility imports
                if (dec instanceof ShortFacilityModuleDec) {
                    FacilityDec facDec =
                            ((ShortFacilityModuleDec) dec).getDec();
                    dec =
                            mySymbolTable.getModuleScope(
                                    new ModuleIdentifier(facDec
                                            .getConceptName().getName()))
                                    .getDefiningElement();
                }

                if (dec instanceof ConceptModuleDec
                        && !importedConceptName.contains(dec.getName()
                                .getName())) {
                    contraintExpList =
                            ((ConceptModuleDec) dec).getConstraints();

                    // Copy all the constraints
                    for (Exp e : contraintExpList) {
                        // Deep copy and set the location detail
                        Exp constraint = Exp.copy(e);
                        if (constraint.getLocation() != null) {
                            Location theLoc = constraint.getLocation();
                            theLoc.setDetails("Constraint of Module: "
                                    + dec.getName());
                            Utilities.setLocation(constraint, theLoc);
                        }

                        // Form conjunct if needed.
                        if (retExp == null) {
                            retExp = Exp.copy(e);
                        }
                        else {
                            retExp =
                                    myTypeGraph.formConjunct(retExp, Exp
                                            .copy(e));
                        }
                    }

                    // Avoid importing constraints for the same concept twice
                    importedConceptName.add(dec.getName().getName());
                }
            }
            catch (NoSuchSymbolException e) {
                System.err.println("Module " + mi.toString()
                        + " does not exist or is not in scope.");
                Utilities.noSuchModule(loc);
            }
        }

        return retExp;
    }

    /**
     * <p>Returns the ensures clause for the current <code>Dec</code>.</p>
     *
     * @param location The location of the ensures clause.
     * @param dec The corresponding <code>Dec</code>.
     *
     * @return The ensures clause <code>Exp</code>.
     */
    private Exp getEnsuresClause(Location location, Dec dec) {
        PosSymbol name = dec.getName();
        Exp ensures = null;
        Exp retExp;

        // Check for each kind of ModuleDec possible
        if (dec instanceof FacilityOperationDec) {
            ensures = ((FacilityOperationDec) dec).getEnsures();
        }
        else if (dec instanceof OperationDec) {
            ensures = ((OperationDec) dec).getEnsures();
        }

        // Deep copy and fill in the details of this location
        if (ensures != null) {
            retExp = Exp.copy(ensures);
        }
        else {
            retExp = myTypeGraph.getTrueVarExp();
        }

        if (location != null) {
            Location loc = (Location) location.clone();
            loc.setDetails("Ensures Clause of " + name);
            Utilities.setLocation(retExp, loc);
        }

        return retExp;
    }

    /**
     * <p>Returns all the constraint clauses combined together for the
     * for the list of module parameters.</p>
     *
     * @param loc The location of the <code>ModuleDec</code>.
     * @param moduleParameterDecs The list of parameter for this module.
     *
     * @return The constraint clause <code>Exp</code>.
     */
    private Exp getModuleTypeConstraint(Location loc,
            List<ModuleParameterDec> moduleParameterDecs) {
        Exp retVal = myTypeGraph.getTrueVarExp();
        for (ModuleParameterDec m : moduleParameterDecs) {
            Dec wrappedDec = m.getWrappedDec();
            if (wrappedDec instanceof ConstantParamDec) {
                ConstantParamDec dec = (ConstantParamDec) wrappedDec;
                ProgramTypeEntry typeEntry;

                if (dec.getTy() instanceof NameTy) {
                    NameTy pNameTy = (NameTy) dec.getTy();

                    // Query for the type entry in the symbol table
                    SymbolTableEntry ste =
                            Utilities.searchProgramType(pNameTy.getLocation(),
                                    pNameTy.getQualifier(), pNameTy.getName(),
                                    myCurrentModuleScope);

                    if (ste instanceof ProgramTypeEntry) {
                        typeEntry =
                                ste.toProgramTypeEntry(pNameTy.getLocation());
                    }
                    else {
                        typeEntry =
                                ste.toRepresentationTypeEntry(
                                        pNameTy.getLocation())
                                        .getDefiningTypeEntry();
                    }

                    // Make sure we don't have a generic type
                    if (typeEntry.getDefiningElement() instanceof TypeDec) {
                        // Obtain the original dec from the AST
                        TypeDec type = (TypeDec) typeEntry.getDefiningElement();

                        // Create a variable expression from the declared variable
                        VarExp varDecExp =
                                Utilities.createVarExp(dec.getLocation(), null,
                                        dec.getName(),
                                        typeEntry.getModelType(), null);

                        // Create a variable expression from the type exemplar
                        VarExp exemplar =
                                Utilities.createVarExp(type.getLocation(),
                                        null, type.getExemplar(), typeEntry
                                                .getModelType(), null);

                        // Deep copy the original constraint clause
                        Exp constraint = Exp.copy(type.getConstraint());
                        constraint =
                                Utilities.replace(constraint, exemplar,
                                        varDecExp);

                        // Conjunct to our other constraints (if any)
                        if (!constraint.isLiteralTrue()) {
                            if (retVal.isLiteralTrue()) {
                                retVal = constraint;
                            }
                            else {
                                retVal =
                                        myTypeGraph.formConjunct(retVal,
                                                constraint);
                            }
                        }
                    }
                }
                else {
                    Utilities.tyNotHandled(dec.getTy(), loc);
                }
            }
        }

        return retVal;
    }

    /**
     * <p>Returns the requires clause for the current <code>Dec</code>.</p>
     *
     * @param location The location of the requires clause.
     * @param dec The corresponding <code>Dec</code>.
     *
     * @return The requires clause <code>Exp</code>.
     */
    private Exp getRequiresClause(Location location, Dec dec) {
        PosSymbol name = dec.getName();
        Exp requires = null;
        Exp retExp;

        // Check for each kind of ModuleDec possible
        if (dec instanceof FacilityOperationDec) {
            requires = ((FacilityOperationDec) dec).getRequires();
        }
        else if (dec instanceof OperationDec) {
            requires = ((OperationDec) dec).getRequires();
        }
        else if (dec instanceof ConceptModuleDec) {
            requires = ((ConceptModuleDec) dec).getRequirement();
        }
        else if (dec instanceof ConceptBodyModuleDec) {
            requires = ((ConceptBodyModuleDec) dec).getRequires();
        }
        else if (dec instanceof EnhancementModuleDec) {
            requires = ((EnhancementModuleDec) dec).getRequirement();
        }
        else if (dec instanceof EnhancementBodyModuleDec) {
            requires = ((EnhancementBodyModuleDec) dec).getRequires();
        }
        else if (dec instanceof FacilityModuleDec) {
            requires = ((FacilityModuleDec) dec).getRequirement();
        }

        // Deep copy and fill in the details of this location
        if (requires != null) {
            retExp = Exp.copy(requires);
        }
        else {
            retExp = myTypeGraph.getTrueVarExp();
        }

        if (location != null) {
            Location loc = (Location) location.clone();
            loc.setDetails("Requires Clause for " + name);
            Utilities.setLocation(retExp, loc);
        }

        return retExp;
    }

    /**
     * <p>Loop through our stack of incomplete assertive codes.</p>
     */
    private void loopAssertiveCodeStack() {
        // Loop until our to process assertive code stack is empty
        while (!myIncAssertiveCodeStack.empty()) {
            // Set the incoming assertive code as our current assertive
            // code we are working on.
            myCurrentAssertiveCode = myIncAssertiveCodeStack.pop();

            myVCBuffer.append("\n***********************");
            myVCBuffer.append("***********************\n");

            // Append any information that still needs to be added to our
            // Debug VC Buffer
            myVCBuffer.append(myIncAssertiveCodeStackInfo.pop());

            // Apply proof rules
            applyRules();

            myVCBuffer.append("\n***********************");
            myVCBuffer.append("***********************\n");

            // Add it to our list of final assertive codes
            ConfirmStmt confirmStmt = myCurrentAssertiveCode.getFinalConfirm();
            if (!confirmStmt.getAssertion().isLiteralTrue()) {
                myFinalAssertiveCodeList.add(myCurrentAssertiveCode);
            }
            else {
                // Only add true if it is a goal we want to show up.
                if (!confirmStmt.getSimplify()) {
                    myFinalAssertiveCodeList.add(myCurrentAssertiveCode);
                }
            }

            // Set the current assertive code to null
            myCurrentAssertiveCode = null;
        }
    }

    /**
     * <p>Modify the argument expression list if we have a
     * nested function call.</p>
     *
     * @param callArgs The original list of arguments.
     *
     * @return The modified list of arguments.
     */
    private List<Exp> modifyArgumentList(List<ProgramExp> callArgs) {
        // Find all the replacements that needs to happen to the requires
        // and ensures clauses
        List<Exp> replaceArgs = new ArrayList<Exp>();
        for (ProgramExp p : callArgs) {
            // Check for nested function calls in ProgramDotExp
            // and ProgramParamExp.
            if (p instanceof ProgramDotExp || p instanceof ProgramParamExp) {
                NestedFuncWalker nfw =
                        new NestedFuncWalker(myCurrentOperationEntry,
                                myOperationDecreasingExp, mySymbolTable,
                                myCurrentModuleScope, myCurrentAssertiveCode,
                                myInstantiatedFacilityArgMap);
                TreeWalker tw = new TreeWalker(nfw);
                tw.visit(p);

                // Add the requires clause as something we need to confirm
                Exp pRequires = nfw.getRequiresClause();
                if (!pRequires.isLiteralTrue()) {
                    myCurrentAssertiveCode.addConfirm(pRequires.getLocation(),
                            pRequires, false);
                }

                // Add the modified ensures clause as the new expression we want
                // to replace in the CallStmt's ensures clause.
                replaceArgs.add(nfw.getEnsuresClause());
            }
            // For all other types of arguments, simply add it to the list to be replaced
            else {
                replaceArgs.add(p);
            }
        }

        return replaceArgs;
    }

    /**
     * <p>Modifies the ensures clause based on the parameter mode.</p>
     *
     * @param ensures The <code>Exp</code> containing the ensures clause.
     * @param opLocation The <code>Location</code> for the operation
     * @param opName The name of the operation.
     * @param parameterVarDecList The list of parameter variables for the operation.
     * @param isLocal True if it is a local operation, false otherwise.
     *
     * @return The modified ensures clause <code>Exp</code>.
     */
    private Exp modifyEnsuresByParameter(Exp ensures, Location opLocation,
            String opName, List<ParameterVarDec> parameterVarDecList,
            boolean isLocal) {
        // Loop through each parameter
        for (ParameterVarDec p : parameterVarDecList) {
            // Ty is NameTy
            if (p.getTy() instanceof NameTy) {
                NameTy pNameTy = (NameTy) p.getTy();

                // Exp form of the parameter variable
                VarExp parameterExp =
                        new VarExp(p.getLocation(), null, p.getName().copy());
                parameterExp.setMathType(pNameTy.getMathTypeValue());

                // Create an old exp (#parameterExp)
                OldExp oldParameterExp =
                        new OldExp(p.getLocation(), Exp.copy(parameterExp));
                oldParameterExp.setMathType(pNameTy.getMathTypeValue());

                // Query for the type entry in the symbol table
                SymbolTableEntry ste =
                        Utilities.searchProgramType(pNameTy.getLocation(),
                                pNameTy.getQualifier(), pNameTy.getName(),
                                myCurrentModuleScope);

                ProgramTypeEntry typeEntry;
                if (ste instanceof ProgramTypeEntry) {
                    typeEntry = ste.toProgramTypeEntry(pNameTy.getLocation());
                }
                else {
                    typeEntry =
                            ste
                                    .toRepresentationTypeEntry(
                                            pNameTy.getLocation())
                                    .getDefiningTypeEntry();
                }

                // Restores mode
                // TODO: Preserves mode needs to be syntaticlly checked.
                if (p.getMode() == Mode.RESTORES) {
                    // Set the details for the new location
                    Location restoresLoc;
                    if (ensures != null && ensures.getLocation() != null) {
                        Location enLoc = ensures.getLocation();
                        restoresLoc = ((Location) enLoc.clone());
                    }
                    else {
                        restoresLoc = ((Location) opLocation.clone());
                        restoresLoc.setDetails("Ensures Clause of " + opName);
                    }
                    restoresLoc.setDetails(restoresLoc.getDetails()
                            + " (Condition from \"" + p.getMode().getModeName()
                            + "\" parameter mode)");

                    // Need to ensure here that the everything inside the type family
                    // is restored at the end of the operation.
                    Exp restoresConditionExp = null;
                    if (typeEntry.getModelType() instanceof MTCartesian) {
                        MTCartesian cartesian =
                                (MTCartesian) typeEntry.getModelType();
                        List<MTType> elementTypes =
                                cartesian.getComponentTypes();
                        for (int i = 0; i < cartesian.size(); i++) {
                            // Retrieve the information on each cartesian product element
                            PosSymbol name =
                                    Utilities.createPosSymbol(cartesian
                                            .getTag(i));
                            MTType type = elementTypes.get(i);

                            // Create a list of segments. The first element should be the original
                            // parameterExp and oldParameterExp and the second element the cartesian product element.
                            edu.clemson.cs.r2jt.collections.List<Exp> segments =
                                    new edu.clemson.cs.r2jt.collections.List<Exp>();
                            edu.clemson.cs.r2jt.collections.List<Exp> oldSegments =
                                    new edu.clemson.cs.r2jt.collections.List<Exp>();
                            segments.add(Exp.copy(parameterExp));
                            oldSegments.add(Exp.copy(oldParameterExp));
                            segments.add(Utilities.createVarExp(
                                    (Location) opLocation.clone(), null, name
                                            .copy(), type, null));
                            oldSegments.add(Utilities.createVarExp(
                                    (Location) opLocation.clone(), null, name
                                            .copy(), type, null));

                            // Create the dotted expressions
                            DotExp elementDotExp =
                                    Utilities.createDotExp(
                                            (Location) opLocation.clone(),
                                            segments, type);
                            DotExp oldElementDotExp =
                                    Utilities.createDotExp(
                                            (Location) opLocation.clone(),
                                            oldSegments, type);

                            // Create an equality expression
                            EqualsExp equalsExp =
                                    new EqualsExp(opLocation, elementDotExp,
                                            EqualsExp.EQUAL, oldElementDotExp);
                            equalsExp.setMathType(BOOLEAN);
                            equalsExp.setLocation((Location) restoresLoc
                                    .clone());

                            // Add this to our final equals expression
                            if (restoresConditionExp == null) {
                                restoresConditionExp = equalsExp;
                            }
                            else {
                                restoresConditionExp =
                                        myTypeGraph
                                                .formConjunct(
                                                        restoresConditionExp,
                                                        equalsExp);
                            }
                        }
                    }
                    else {
                        // Construct an expression using the expression and it's
                        // old expression equivalent.
                        restoresConditionExp =
                                new EqualsExp(opLocation, Exp
                                        .copy(parameterExp), EqualsExp.EQUAL,
                                        Exp.copy(oldParameterExp));
                        restoresConditionExp.setMathType(BOOLEAN);
                        restoresConditionExp.setLocation(restoresLoc);
                    }

                    // Create an AND infix expression with the ensures clause
                    if (ensures != null
                            && !ensures.equals(myTypeGraph.getTrueVarExp())) {
                        Location newEnsuresLoc =
                                (Location) ensures.getLocation().clone();
                        ensures =
                                myTypeGraph.formConjunct(ensures,
                                        restoresConditionExp);
                        ensures.setLocation(newEnsuresLoc);
                    }
                    // Make new expression the ensures clause
                    else {
                        ensures = restoresConditionExp;
                    }
                }
                // Clears mode
                else if (p.getMode() == Mode.CLEARS) {
                    Exp init;
                    if (typeEntry.getDefiningElement() instanceof TypeDec) {
                        // Obtain the original dec from the AST
                        TypeDec type = (TypeDec) typeEntry.getDefiningElement();

                        // Obtain the exemplar in VarExp form
                        VarExp exemplar =
                                new VarExp(null, null, type.getExemplar());
                        exemplar.setMathType(pNameTy.getMathTypeValue());

                        // Deep copy the original initialization ensures and the constraint
                        init = Exp.copy(type.getInitialization().getEnsures());

                        // Replace the formal with the actual
                        init = Utilities.replace(init, exemplar, parameterExp);

                        // Set the details for the new location
                        Location initLoc;
                        if (ensures != null && ensures.getLocation() != null) {
                            Location reqLoc = ensures.getLocation();
                            initLoc = ((Location) reqLoc.clone());
                        }
                        else {
                            initLoc = ((Location) opLocation.clone());
                            initLoc.setDetails("Ensures Clause of " + opName);
                        }
                        initLoc.setDetails(initLoc.getDetails()
                                + " (Condition from \""
                                + p.getMode().getModeName()
                                + "\" parameter mode)");
                        Utilities.setLocation(init, initLoc);
                    }
                    // Since the type is generic, we can only use the is_initial predicate
                    // to ensure that the value is initial value.
                    else {
                        // Obtain the original dec from the AST
                        Location varLoc = p.getLocation();

                        // Create an is_initial dot expression
                        init =
                                Utilities.createInitExp(new VarDec(p.getName(),
                                        p.getTy()), MTYPE, BOOLEAN);
                        if (varLoc != null) {
                            Location loc = (Location) varLoc.clone();
                            loc.setDetails("Initial Value for "
                                    + p.getName().getName());
                            Utilities.setLocation(init, loc);
                        }
                    }

                    // Create an AND infix expression with the ensures clause
                    if (ensures != null) {
                        Location newEnsuresLoc =
                                (Location) ensures.getLocation().clone();
                        ensures = myTypeGraph.formConjunct(ensures, init);
                        ensures.setLocation(newEnsuresLoc);
                    }
                    // Make initialization expression the ensures clause
                    else {
                        ensures = init;
                    }
                }

                // If the type is a type representation, then our requires clause
                // should really say something about the conceptual type and not
                // the variable
                if (ste instanceof RepresentationTypeEntry && !isLocal) {
                    Exp conceptualExp =
                            Utilities.createConcVarExp(opLocation,
                                    parameterExp, parameterExp.getMathType(),
                                    BOOLEAN);
                    OldExp oldConceptualExp =
                            new OldExp(opLocation, Exp.copy(conceptualExp));
                    ensures =
                            Utilities.replace(ensures, parameterExp,
                                    conceptualExp);
                    ensures =
                            Utilities.replace(ensures, oldParameterExp,
                                    oldConceptualExp);
                }
            }
            else {
                // Ty not handled.
                Utilities.tyNotHandled(p.getTy(), p.getLocation());
            }
        }

        // Replace facility actuals variables in the ensures clause
        ensures =
                Utilities.replaceFacilityFormalWithActual(opLocation, ensures,
                        parameterVarDecList, myInstantiatedFacilityArgMap,
                        myCurrentModuleScope);

        return ensures;
    }

    /**
     * <p>Returns the ensures clause.</p>
     *
     * @param ensures The <code>Exp</code> containing the ensures clause.
     * @param opLocation The <code>Location</code> for the operation.
     * @param operationDec The <code>OperationDec</code> that is modifying the ensures clause.
     * @param isLocal True if it is a local operation, false otherwise.
     *
     * @return The modified ensures clause <code>Exp</code>.
     */
    private Exp modifyEnsuresClause(Exp ensures, Location opLocation,
            OperationDec operationDec, boolean isLocal) {
        // Modifies the existing ensures clause based on
        // the parameter modes.
        ensures =
                modifyEnsuresByParameter(ensures, opLocation, operationDec
                        .getName().getName(), operationDec.getParameters(),
                        isLocal);

        return ensures;
    }

    /**
     * <p>Modifies the requires clause based on .</p>
     *
     * @param requires The <code>Exp</code> containing the requires clause.
     *
     * @return The modified requires clause <code>Exp</code>.
     */
    private Exp modifyRequiresByGlobalMode(Exp requires) {
        return requires;
    }

    /**
     * <p>Modifies the requires clause based on the parameter mode.</p>
     *
     * @param requires The <code>Exp</code> containing the requires clause.
     * @param opLocation The <code>Location</code> for the operation.
     * @param assertiveCode The current assertive code we are currently generating.
     * @param operationDec The <code>OperationDec</code> that is modifying the requires clause.
     * @param isLocal True if it is a local operation, false otherwise.
     *
     * @return The modified requires clause <code>Exp</code>.
     */
    private Exp modifyRequiresByParameter(Exp requires, Location opLocation,
            AssertiveCode assertiveCode, OperationDec operationDec,
            boolean isLocal) {
        // Obtain the list of parameters
        List<ParameterVarDec> parameterVarDecList =
                operationDec.getParameters();

        // Loop through each parameter
        for (ParameterVarDec p : parameterVarDecList) {
            ProgramTypeEntry typeEntry;

            // Ty is NameTy
            if (p.getTy() instanceof NameTy) {
                NameTy pNameTy = (NameTy) p.getTy();
                PTType ptType = pNameTy.getProgramTypeValue();

                // Only deal with actual types and don't deal
                // with entry types passed in to the concept realization
                if (!(ptType instanceof PTGeneric)) {
                    // Convert p to a VarExp
                    VarExp parameterExp = new VarExp(null, null, p.getName());
                    parameterExp.setMathType(pNameTy.getMathTypeValue());

                    // Query for the type entry in the symbol table
                    SymbolTableEntry ste =
                            Utilities.searchProgramType(pNameTy.getLocation(),
                                    pNameTy.getQualifier(), pNameTy.getName(),
                                    myCurrentModuleScope);

                    if (ste instanceof ProgramTypeEntry) {
                        typeEntry =
                                ste.toProgramTypeEntry(pNameTy.getLocation());
                    }
                    else {
                        typeEntry =
                                ste.toRepresentationTypeEntry(
                                        pNameTy.getLocation())
                                        .getDefiningTypeEntry();
                    }

                    // Obtain the original dec from the AST
                    VarExp exemplar = null;
                    Exp constraint = null;
                    if (typeEntry.getDefiningElement() instanceof TypeDec) {
                        TypeDec type = (TypeDec) typeEntry.getDefiningElement();

                        // Obtain the exemplar in VarExp form
                        exemplar = new VarExp(null, null, type.getExemplar());
                        exemplar.setMathType(pNameTy.getMathTypeValue());

                        // If we have a type representation, then there are no initialization
                        // or constraint clauses.
                        if (ste instanceof ProgramTypeEntry) {
                            // Deep copy the constraint
                            if (type.getConstraint() != null) {
                                constraint = Exp.copy(type.getConstraint());
                            }
                        }
                    }

                    // Other than the replaces mode, constraints for the
                    // other parameter modes needs to be added
                    // to the requires clause as conjuncts.
                    if (p.getMode() != Mode.REPLACES) {
                        if (constraint != null
                                && !constraint.equals(myTypeGraph
                                        .getTrueVarExp())) {
                            // Replace the formal with the actual
                            if (exemplar != null) {
                                constraint =
                                        Utilities.replace(constraint, exemplar,
                                                parameterExp);
                            }

                            // Set the details for the new location
                            if (constraint.getLocation() != null) {
                                Location constLoc;
                                if (requires != null
                                        && requires.getLocation() != null) {
                                    Location reqLoc = requires.getLocation();
                                    constLoc = ((Location) reqLoc.clone());
                                }
                                else {
                                    // Append the name of the current procedure
                                    String details = "";
                                    if (myCurrentOperationEntry != null) {
                                        details =
                                                " in Procedure "
                                                        + myCurrentOperationEntry
                                                                .getName();
                                    }

                                    constLoc = ((Location) opLocation.clone());
                                    constLoc.setDetails("Requires Clause of "
                                            + operationDec.getName().getName()
                                            + details);
                                }
                                constLoc.setDetails(constLoc.getDetails()
                                        + " (Constraint from \""
                                        + p.getMode().getModeName()
                                        + "\" parameter mode)");
                                constraint.setLocation(constLoc);
                            }

                            // Create an AND infix expression with the requires clause
                            if (requires != null
                                    && !requires.equals(myTypeGraph
                                            .getTrueVarExp())) {
                                requires =
                                        myTypeGraph.formConjunct(requires,
                                                constraint);
                                requires.setLocation((Location) opLocation
                                        .clone());
                            }
                            // Make constraint expression the requires clause
                            else {
                                requires = constraint;
                            }
                        }
                    }

                    // If the type is a type representation, then our requires clause
                    // should really say something about the conceptual type and not
                    // the variable
                    if (ste instanceof RepresentationTypeEntry && !isLocal) {
                        requires =
                                Utilities.replace(requires, parameterExp,
                                        Utilities
                                                .createConcVarExp(opLocation,
                                                        parameterExp,
                                                        parameterExp
                                                                .getMathType(),
                                                        BOOLEAN));
                        requires.setLocation((Location) opLocation.clone());
                    }

                    // If the type is a type representation, then we need to add
                    // all the type constraints from all the variable declarations
                    // in the type representation.
                    if (ste instanceof RepresentationTypeEntry) {
                        Exp repConstraintExp = null;
                        Set<VarExp> keys =
                                myRepresentationConstraintMap.keySet();
                        for (VarExp varExp : keys) {
                            if (varExp.getQualifier() == null
                                    && varExp.getName().getName().equals(
                                            pNameTy.getName().getName())) {
                                if (repConstraintExp == null) {
                                    repConstraintExp =
                                            myRepresentationConstraintMap
                                                    .get(varExp);
                                }
                                else {
                                    Utilities.ambiguousTy(pNameTy, pNameTy
                                            .getLocation());
                                }
                            }
                        }

                        // Only do the following if the expression is not simply true
                        if (!repConstraintExp.isLiteralTrue()) {
                            // Replace the exemplar with the actual parameter variable expression
                            repConstraintExp =
                                    Utilities.replace(repConstraintExp,
                                            exemplar, parameterExp);

                            // Add this to our requires clause
                            requires =
                                    myTypeGraph.formConjunct(requires,
                                            repConstraintExp);
                            requires.setLocation((Location) opLocation.clone());
                        }
                    }
                }

                // Add the current variable to our list of free variables
                assertiveCode.addFreeVar(Utilities.createVarExp(
                        p.getLocation(), null, p.getName(), pNameTy
                                .getMathTypeValue(), null));
            }
            else {
                // Ty not handled.
                Utilities.tyNotHandled(p.getTy(), p.getLocation());
            }
        }

        // Replace facility actuals variables in the requires clause
        requires =
                Utilities.replaceFacilityFormalWithActual(opLocation, requires,
                        parameterVarDecList, myInstantiatedFacilityArgMap,
                        myCurrentModuleScope);

        return requires;
    }

    /**
     * <p>Modifies the requires clause.</p>
     *
     * @param requires The <code>Exp</code> containing the requires clause.
     * @param opLocation The <code>Location</code> for the operation.
     * @param assertiveCode The current assertive code we are currently generating.
     * @param operationDec The <code>OperationDec</code> that is modifying the requires clause.
     * @param isLocal True if it is a local operation, false otherwise.
     *
     * @return The modified requires clause <code>Exp</code>.
     */
    private Exp modifyRequiresClause(Exp requires, Location opLocation,
            AssertiveCode assertiveCode, OperationDec operationDec,
            boolean isLocal) {
        // Modifies the existing requires clause based on
        // the parameter modes.
        requires =
                modifyRequiresByParameter(requires, opLocation, assertiveCode,
                        operationDec, isLocal);

        // Modifies the existing requires clause based on
        // the parameter modes.
        // TODO: Ask Murali what this means
        requires = modifyRequiresByGlobalMode(requires);

        return requires;
    }

    /**
     * <p>Basic sanity check for operations as parameters.</p>
     *
     * @param loc Location of the actual operation as parameter.
     * @param formalParams Formal parameters.
     * @param actualParams Actual parameters.
     */
    private void opAsParameterSanityCheck(Location loc,
            List<ParameterVarDec> formalParams,
            List<ParameterVarDec> actualParams) {
        if (formalParams.size() != actualParams.size()) {
            throw new SourceErrorException(
                    "Actual operation parameter count "
                            + "does not correspond to the formal operation parameter count."
                            + "\n\tExpected count: " + formalParams.size()
                            + "\n\tFound count: " + actualParams.size(), loc);
        }

        Iterator<ParameterVarDec> formalIt = formalParams.iterator();
        Iterator<ParameterVarDec> actualIt = actualParams.iterator();
        ParameterVarDec currFormalParam, currActualParam;
        while (formalIt.hasNext()) {
            currFormalParam = formalIt.next();
            currActualParam = actualIt.next();

            if (!currActualParam.getMode().getModeName().equals(
                    currFormalParam.getMode().getModeName())) {
                throw new SourceErrorException(
                        "Operation parameter modes are not the same."
                                + "\n\tExpecting: "
                                + currFormalParam.getMode().getModeName() + " "
                                + currFormalParam.getName() + "\n\tFound: "
                                + currActualParam.getMode().getModeName() + " "
                                + currActualParam.getName(), loc);
            }
        }
    }

    /**
     * <p>Replace the formal parameter variables with the actual mathematical
     * expressions passed in.</p>
     *
     * @param exp The expression to be replaced.
     * @param actualParamList The list of actual parameter variables.
     * @param formalParamList The list of formal parameter variables.
     *
     * @return The modified expression.
     */
    private Exp replaceFacilityDeclarationVariables(Exp exp,
            List<Exp> formalParamList, List<Exp> actualParamList) {
        Exp retExp = Exp.copy(exp);

        if (formalParamList.size() == actualParamList.size()) {
            // Loop through the argument list
            for (int i = 0; i < formalParamList.size(); i++) {
                // Concept variable
                Exp formalExp = formalParamList.get(i);

                if (formalExp != null) {
                    // Temporary replacement to avoid formal and actuals being the same
                    Exp newFormalExp;
                    if (formalExp instanceof VarExp) {
                        VarExp formalExpAsVarExp = (VarExp) formalExp;
                        newFormalExp =
                                Utilities.createVarExp(null, null, Utilities
                                        .createPosSymbol("_"
                                                + formalExpAsVarExp.getName()),
                                        formalExp.getMathType(), formalExp
                                                .getMathTypeValue());
                    }
                    else {
                        VarExp modifiedInnerVarExp =
                                (VarExp) Exp
                                        .copy(((OldExp) formalExp).getExp());
                        modifiedInnerVarExp.setName(Utilities
                                .createPosSymbol("_"
                                        + modifiedInnerVarExp.getName()
                                                .getName()));
                        newFormalExp =
                                new OldExp(modifiedInnerVarExp.getLocation(),
                                        modifiedInnerVarExp);
                    }
                    retExp = Utilities.replace(retExp, formalExp, newFormalExp);

                    // Actually perform the desired replacement
                    Exp actualExp = actualParamList.get(i);
                    retExp = Utilities.replace(retExp, newFormalExp, actualExp);
                }
            }
        }
        else {
            throw new RuntimeException("Size not equal!");
        }

        return retExp;
    }

    /**
     * <p>Replace the formal with the actual variables
     * inside the ensures clause.</p>
     *
     * @param ensures The ensures clause.
     * @param paramList The list of parameter variables.
     * @param stateVarList The list of state variables.
     * @param argList The list of arguments from the operation call.
     * @param isSimple Check if it is a simple replacement.
     *
     * @return The ensures clause in <code>Exp</code> form.
     */
    private Exp replaceFormalWithActualEns(Exp ensures,
            List<ParameterVarDec> paramList, List<AffectsItem> stateVarList,
            List<Exp> argList, boolean isSimple) {
        // Current final confirm
        Exp newConfirm;

        // List to hold temp and real values of variables in case
        // of duplicate spec and real variables
        List<Exp> undRepList = new ArrayList<Exp>();
        List<Exp> replList = new ArrayList<Exp>();

        // Replace state variables in the ensures clause
        // and create new confirm statements if needed.
        for (int i = 0; i < stateVarList.size(); i++) {
            ConfirmStmt confirmStmt = myCurrentAssertiveCode.getFinalConfirm();
            newConfirm = confirmStmt.getAssertion();
            AffectsItem stateVar = stateVarList.get(i);

            // Only deal with Alters/Reassigns/Replaces/Updates modes
            if (stateVar.getMode() == Mode.ALTERS
                    || stateVar.getMode() == Mode.REASSIGNS
                    || stateVar.getMode() == Mode.REPLACES
                    || stateVar.getMode() == Mode.UPDATES) {
                // Obtain the variable from our free variable list
                Exp globalFreeVar =
                        myCurrentAssertiveCode.getFreeVar(stateVar.getName(),
                                true);
                if (globalFreeVar != null) {
                    VarExp oldNamesVar = new VarExp();
                    oldNamesVar.setName(stateVar.getName());

                    // Create a local free variable if it is not there
                    Exp localFreeVar =
                            myCurrentAssertiveCode.getFreeVar(stateVar
                                    .getName(), false);
                    if (localFreeVar == null) {
                        // TODO: Don't have a type for state variables?
                        localFreeVar =
                                new VarExp(null, null, stateVar.getName());
                        localFreeVar =
                                Utilities.createQuestionMarkVariable(
                                        myTypeGraph.formConjunct(ensures,
                                                newConfirm),
                                        (VarExp) localFreeVar);
                        myCurrentAssertiveCode.addFreeVar(localFreeVar);
                    }
                    else {
                        localFreeVar =
                                Utilities.createQuestionMarkVariable(
                                        myTypeGraph.formConjunct(ensures,
                                                newConfirm),
                                        (VarExp) localFreeVar);
                    }

                    // Creating "#" expressions and replace these in the
                    // ensures clause.
                    OldExp osVar = new OldExp(null, Exp.copy(globalFreeVar));
                    OldExp oldNameOSVar =
                            new OldExp(null, Exp.copy(oldNamesVar));
                    ensures =
                            Utilities.replace(ensures, oldNamesVar,
                                    globalFreeVar);
                    ensures = Utilities.replace(ensures, oldNameOSVar, osVar);

                    // If it is not simple replacement, replace all ensures clauses
                    // with the appropriate expressions.
                    if (!isSimple) {
                        ensures =
                                Utilities.replace(ensures, globalFreeVar,
                                        localFreeVar);
                        ensures =
                                Utilities
                                        .replace(ensures, osVar, globalFreeVar);
                        newConfirm =
                                Utilities.replace(newConfirm, globalFreeVar,
                                        localFreeVar);
                    }

                    // Set newConfirm as our new final confirm statement
                    myCurrentAssertiveCode.setFinalConfirm(newConfirm,
                            confirmStmt.getSimplify());
                }
                // Error: Why isn't it a free variable.
                else {
                    Utilities.notInFreeVarList(stateVar.getName(), stateVar
                            .getLocation());
                }
            }
        }

        // Replace postcondition variables in the ensures clause
        for (int i = 0; i < argList.size(); i++) {
            ParameterVarDec varDec = paramList.get(i);
            Exp exp = argList.get(i);
            PosSymbol VDName = varDec.getName();
            ConfirmStmt confirmStmt = myCurrentAssertiveCode.getFinalConfirm();
            newConfirm = confirmStmt.getAssertion();

            // VarExp form of the parameter variable
            VarExp oldExp = new VarExp(null, null, VDName);
            oldExp.setMathType(exp.getMathType());
            oldExp.setMathTypeValue(exp.getMathTypeValue());

            // Convert the pExp into a something we can use
            Exp repl = Utilities.convertExp(exp, myCurrentModuleScope);
            Exp undqRep = null, quesRep = null;
            OldExp oSpecVar, oRealVar;
            String replName = null;

            // Case #1: ProgramIntegerExp
            // Case #2: ProgramCharExp
            // Case #3: ProgramStringExp
            if (exp instanceof ProgramIntegerExp
                    || exp instanceof ProgramCharExp
                    || exp instanceof ProgramStringExp) {
                Exp convertExp =
                        Utilities.convertExp(exp, myCurrentModuleScope);
                if (exp instanceof ProgramIntegerExp) {
                    replName =
                            Integer.toString(((IntegerExp) convertExp)
                                    .getValue());
                }
                else if (exp instanceof ProgramCharExp) {
                    replName =
                            Character.toString(((CharExp) convertExp)
                                    .getValue());
                }
                else {
                    replName = ((StringExp) convertExp).getValue();
                }

                // Create a variable expression of the form "_?[Argument Name]"
                undqRep =
                        Utilities.createVarExp(null, null, Utilities
                                .createPosSymbol("_?" + replName), exp
                                .getMathType(), exp.getMathTypeValue());

                // Create a variable expression of the form "?[Argument Name]"
                quesRep =
                        Utilities.createVarExp(null, null, Utilities
                                .createPosSymbol("?" + replName), exp
                                .getMathType(), exp.getMathTypeValue());
            }
            // Case #4: VariableDotExp
            else if (exp instanceof VariableDotExp) {
                if (repl instanceof DotExp) {
                    Exp pE = ((DotExp) repl).getSegments().get(0);
                    replName = pE.toString(0);

                    // Create a variable expression of the form "_?[Argument Name]"
                    undqRep = Exp.copy(repl);
                    edu.clemson.cs.r2jt.collections.List<Exp> segList =
                            ((DotExp) undqRep).getSegments();
                    VariableNameExp undqNameRep =
                            new VariableNameExp(null, null, Utilities
                                    .createPosSymbol("_?" + replName));
                    undqNameRep.setMathType(pE.getMathType());
                    segList.set(0, undqNameRep);
                    ((DotExp) undqRep).setSegments(segList);

                    // Create a variable expression of the form "?[Argument Name]"
                    quesRep = Exp.copy(repl);
                    segList = ((DotExp) quesRep).getSegments();
                    segList.set(0, ((VariableDotExp) exp).getSegments().get(0));
                    ((DotExp) quesRep).setSegments(segList);
                }
                else if (repl instanceof VariableDotExp) {
                    Exp pE = ((VariableDotExp) repl).getSegments().get(0);
                    replName = pE.toString(0);

                    // Create a variable expression of the form "_?[Argument Name]"
                    undqRep = Exp.copy(repl);
                    edu.clemson.cs.r2jt.collections.List<VariableExp> segList =
                            ((VariableDotExp) undqRep).getSegments();
                    VariableNameExp undqNameRep =
                            new VariableNameExp(null, null, Utilities
                                    .createPosSymbol("_?" + replName));
                    undqNameRep.setMathType(pE.getMathType());
                    segList.set(0, undqNameRep);
                    ((VariableDotExp) undqRep).setSegments(segList);

                    // Create a variable expression of the form "?[Argument Name]"
                    quesRep = Exp.copy(repl);
                    segList = ((VariableDotExp) quesRep).getSegments();
                    segList.set(0, ((VariableDotExp) exp).getSegments().get(0));
                    ((VariableDotExp) quesRep).setSegments(segList);
                }
                // Error: Case not handled!
                else {
                    Utilities.expNotHandled(exp, exp.getLocation());
                }
            }
            // Case #5: VariableNameExp
            else if (exp instanceof VariableNameExp) {
                // Name of repl in string form
                replName = ((VariableNameExp) exp).getName().getName();

                // Create a variable expression of the form "_?[Argument Name]"
                undqRep =
                        Utilities.createVarExp(null, null, Utilities
                                .createPosSymbol("_?" + replName), exp
                                .getMathType(), exp.getMathTypeValue());

                // Create a variable expression of the form "?[Argument Name]"
                quesRep =
                        Utilities.createVarExp(null, null, Utilities
                                .createPosSymbol("?" + replName), exp
                                .getMathType(), exp.getMathTypeValue());
            }
            // Case #6: Result from a nested function call
            else {
                // Name of repl in string form
                replName = varDec.getName().getName();

                // Create a variable expression of the form "_?[Argument Name]"
                undqRep =
                        Utilities.createVarExp(null, null, Utilities
                                .createPosSymbol("_?" + replName), exp
                                .getMathType(), exp.getMathTypeValue());

                // Create a variable expression of the form "?[Argument Name]"
                quesRep =
                        Utilities.createVarExp(null, null, Utilities
                                .createPosSymbol("?" + replName), exp
                                .getMathType(), exp.getMathTypeValue());
            }

            // "#" versions of oldExp and repl
            oSpecVar = new OldExp(null, Exp.copy(oldExp));
            oRealVar = new OldExp(null, Exp.copy(repl));

            // Replacement map to use substitute.
            Map<Exp, Exp> replacementMap = new HashMap<Exp, Exp>();

            // Nothing can be null!
            if (oldExp != null && quesRep != null && oSpecVar != null
                    && repl != null && oRealVar != null) {
                // Alters, Clears, Reassigns, Replaces, Updates
                if (varDec.getMode() == Mode.ALTERS
                        || varDec.getMode() == Mode.CLEARS
                        || varDec.getMode() == Mode.REASSIGNS
                        || varDec.getMode() == Mode.REPLACES
                        || varDec.getMode() == Mode.UPDATES) {
                    Exp quesVar;

                    // Obtain the free variable
                    VarExp freeVar =
                            (VarExp) myCurrentAssertiveCode.getFreeVar(
                                    Utilities.createPosSymbol(replName), false);
                    if (freeVar == null) {
                        freeVar =
                                Utilities
                                        .createVarExp(
                                                varDec.getLocation(),
                                                null,
                                                Utilities
                                                        .createPosSymbol(replName),
                                                varDec.getTy()
                                                        .getMathTypeValue(),
                                                null);
                    }

                    // Apply the question mark to the free variable
                    freeVar =
                            Utilities
                                    .createQuestionMarkVariable(myTypeGraph
                                            .formConjunct(ensures, newConfirm),
                                            freeVar);

                    if (exp instanceof ProgramDotExp
                            || exp instanceof VariableDotExp) {
                        // Make a copy from repl
                        quesVar = Exp.copy(repl);

                        // Replace the free variable in the question mark variable as the first element
                        // in the dot expression.
                        VarExp tmpVar =
                                new VarExp(null, null, freeVar.getName());
                        tmpVar.setMathType(myTypeGraph.BOOLEAN);
                        edu.clemson.cs.r2jt.collections.List<Exp> segs =
                                ((DotExp) quesVar).getSegments();
                        segs.set(0, tmpVar);
                        ((DotExp) quesVar).setSegments(segs);
                    }
                    else {
                        // Create a variable expression from free variable
                        quesVar = new VarExp(null, null, freeVar.getName());
                        quesVar.setMathType(freeVar.getMathType());
                        quesVar.setMathTypeValue(freeVar.getMathTypeValue());
                    }

                    // Add the new free variable to free variable list
                    myCurrentAssertiveCode.addFreeVar(freeVar);

                    // Check if our ensures clause has the parameter variable in it.
                    if (ensures.containsVar(VDName.getName(), true)
                            || ensures.containsVar(VDName.getName(), false)) {
                        // Replace the ensures clause
                        replacementMap.put(oldExp, undqRep);
                        replacementMap.put(oSpecVar, repl);
                        ensures = ensures.substitute(replacementMap);

                        // Add it to our list of variables to be replaced later
                        undRepList.add(undqRep);
                        replList.add(quesVar);
                    }
                    else {
                        // Replace the ensures clause
                        replacementMap.put(oldExp, quesRep);
                        replacementMap.put(oSpecVar, repl);
                        ensures = ensures.substitute(replacementMap);
                    }

                    // Update our final confirm with the parameter argument
                    newConfirm = Utilities.replace(newConfirm, repl, quesVar);
                    myCurrentAssertiveCode.setFinalConfirm(newConfirm,
                            confirmStmt.getSimplify());
                }
                // All other modes
                else {
                    // Check if our ensures clause has the parameter variable in it.
                    if (ensures.containsVar(VDName.getName(), true)
                            || ensures.containsVar(VDName.getName(), false)) {
                        // Replace the ensures clause
                        replacementMap.put(oldExp, undqRep);
                        replacementMap.put(oSpecVar, undqRep);
                        ensures = ensures.substitute(replacementMap);

                        // Add it to our list of variables to be replaced later
                        undRepList.add(undqRep);
                        replList.add(repl);
                    }
                    else {
                        // Replace the ensures clause
                        replacementMap.put(oldExp, repl);
                        replacementMap.put(oSpecVar, repl);
                        ensures = ensures.substitute(replacementMap);
                    }
                }
            }
        }

        // Replace the temp values with the actual values
        Map<Exp, Exp> replacementMap = new HashMap<Exp, Exp>();
        for (int i = 0; i < undRepList.size(); i++) {
            replacementMap.put(undRepList.get(i), replList.get(i));
        }
        ensures = ensures.substitute(replacementMap);

        return ensures;
    }

    /**
     * <p>Replace the formal with the actual variables
     * inside the requires clause.</p>
     *
     * @param requires The requires clause.
     * @param paramList The list of parameter variables.
     * @param argList The list of arguments from the operation call.
     *
     * @return The requires clause in <code>Exp</code> form.
     */
    private Exp replaceFormalWithActualReq(Exp requires,
            List<ParameterVarDec> paramList, List<Exp> argList) {
        // List to hold temp and real values of variables in case
        // of duplicate spec and real variables
        List<Exp> undRepList = new ArrayList<Exp>();
        List<Exp> replList = new ArrayList<Exp>();

        // Replace precondition variables in the requires clause
        for (int i = 0; i < argList.size(); i++) {
            ParameterVarDec varDec = paramList.get(i);
            Exp exp = argList.get(i);

            // Convert the pExp into a something we can use
            Exp repl = Utilities.convertExp(exp, myCurrentModuleScope);

            // VarExp form of the parameter variable
            VarExp oldExp =
                    Utilities.createVarExp(null, null, varDec.getName(), exp
                            .getMathType(), exp.getMathTypeValue());

            // New VarExp
            VarExp newExp =
                    Utilities.createVarExp(null, null, Utilities
                            .createPosSymbol("_" + varDec.getName().getName()),
                            repl.getMathType(), repl.getMathTypeValue());

            // Replace the old with the new in the requires clause
            requires = Utilities.replace(requires, oldExp, newExp);

            // Add it to our list
            undRepList.add(newExp);
            replList.add(repl);
        }

        // Replace the temp values with the actual values
        for (int i = 0; i < undRepList.size(); i++) {
            requires =
                    Utilities.replace(requires, undRepList.get(i), replList
                            .get(i));
        }

        return requires;
    }

    // -----------------------------------------------------------
    // Proof Rules
    // -----------------------------------------------------------

    /**
     * <p>Applies the assume rule to the
     * <code>Statement</code>.</p>
     *
     * @param stmt Our current <code>AssumeStmt</code>.
     */
    private void applyAssumeStmtRule(AssumeStmt stmt) {
        // Check to see if our assertion just has "True"
        Exp assertion = stmt.getAssertion();
        if (assertion instanceof VarExp
                && assertion.equals(myTypeGraph.getTrueVarExp())) {
            // Verbose Mode Debug Messages
            myVCBuffer.append("\nAssume Rule Applied and Simplified: \n");
            myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
            myVCBuffer.append("\n_____________________ \n");
        }
        else {
            // Apply simplification for equals expressions and
            // apply steps to generate parsimonious vcs.
            ConfirmStmt finalConfirm = myCurrentAssertiveCode.getFinalConfirm();
            boolean simplify = finalConfirm.getSimplify();
            List<Exp> assumeExpList =
                    Utilities.splitConjunctExp(stmt.getAssertion(),
                            new ArrayList<Exp>());
            List<Exp> confirmExpList =
                    Utilities.splitConjunctExp(finalConfirm.getAssertion(),
                            new ArrayList<Exp>());

            Exp currentFinalConfirm =
                    formParsimoniousVC(confirmExpList, assumeExpList, stmt
                            .getIsStipulate());

            // Set this as our new final confirm
            myCurrentAssertiveCode.setFinalConfirm(currentFinalConfirm,
                    simplify);

            // Verbose Mode Debug Messages
            myVCBuffer.append("\nAssume Rule Applied: \n");
            myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
            myVCBuffer.append("\n_____________________ \n");
        }
    }

    /**
     *  <p>Applies the change rule.</p>
     *
     * @param change The change clause
     */
    private void applyChangeRule(VerificationStatement change) {
        List<VariableExp> changeList =
                (List<VariableExp>) change.getAssertion();
        ConfirmStmt confirmStmt = myCurrentAssertiveCode.getFinalConfirm();
        Exp finalConfirm = confirmStmt.getAssertion();

        // Loop through each variable
        for (VariableExp v : changeList) {
            // v is an instance of VariableNameExp
            if (v instanceof VariableNameExp) {
                VariableNameExp vNameExp = (VariableNameExp) v;

                // Create VarExp for vNameExp
                VarExp vExp =
                        Utilities.createVarExp(vNameExp.getLocation(), vNameExp
                                .getQualifier(), vNameExp.getName(), vNameExp
                                .getMathType(), vNameExp.getMathTypeValue());

                // Create a new question mark variable
                VarExp newV =
                        Utilities
                                .createQuestionMarkVariable(finalConfirm, vExp);

                // Add this new variable to our list of free variables
                myCurrentAssertiveCode.addFreeVar(newV);

                // Replace all instances of vExp with newV
                finalConfirm = Utilities.replace(finalConfirm, vExp, newV);
            }
        }

        // Set the modified statement as our new final confirm
        myCurrentAssertiveCode.setFinalConfirm(finalConfirm, confirmStmt
                .getSimplify());

        // Verbose Mode Debug Messages
        myVCBuffer.append("\nChange Rule Applied: \n");
        myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
        myVCBuffer.append("\n_____________________ \n");
    }

    /**
     * <p>Applies the call statement rule to the
     * <code>Statement</code>.</p>
     *
     * @param stmt Our current <code>CallStmt</code>.
     */
    private void applyCallStmtRule(CallStmt stmt) {
        // Call a method to locate the operation dec for this call
        List<PTType> argTypes = new LinkedList<PTType>();
        for (ProgramExp arg : stmt.getArguments()) {
            argTypes.add(arg.getProgramType());
        }
        OperationEntry opEntry =
                Utilities.searchOperation(stmt.getLocation(), stmt
                        .getQualifier(), stmt.getName(), argTypes,
                        myCurrentModuleScope);
        OperationDec opDec = Utilities.convertToOperationDec(opEntry);
        boolean isLocal =
                Utilities.isLocationOperation(stmt.getName().getName(),
                        myCurrentModuleScope);

        // Get the ensures clause for this operation
        // Note: If there isn't an ensures clause, it is set to "True"
        Exp ensures;
        if (opDec.getEnsures() != null) {
            ensures = Exp.copy(opDec.getEnsures());
        }
        else {
            ensures = myTypeGraph.getTrueVarExp();
            Location loc;
            if (opDec.getLocation() != null) {
                loc = (Location) opDec.getLocation().clone();
            }
            else {
                loc = (Location) opDec.getEnsures().getLocation().clone();
            }
            ensures.setLocation(loc);
        }

        // Check for recursive call of itself
        if (myCurrentOperationEntry != null
                && myOperationDecreasingExp != null
                && myCurrentOperationEntry.getName().equals(opEntry.getName())
                && myCurrentOperationEntry.getReturnType().equals(
                        opEntry.getReturnType())
                && myCurrentOperationEntry.getSourceModuleIdentifier().equals(
                        opEntry.getSourceModuleIdentifier())) {
            // Create a new confirm statement using P_val and the decreasing clause
            VarExp pVal =
                    Utilities.createPValExp(myOperationDecreasingExp
                            .getLocation(), myCurrentModuleScope);

            // Create a new infix expression
            IntegerExp oneExp = new IntegerExp();
            oneExp.setValue(1);
            oneExp.setMathType(myOperationDecreasingExp.getMathType());
            InfixExp leftExp =
                    new InfixExp(stmt.getLocation(), oneExp, Utilities
                            .createPosSymbol("+"), Exp
                            .copy(myOperationDecreasingExp));
            leftExp.setMathType(myOperationDecreasingExp.getMathType());
            InfixExp exp =
                    Utilities.createLessThanEqExp(stmt.getLocation(), leftExp,
                            pVal, BOOLEAN);

            // Create the new confirm statement
            Location loc;
            if (myOperationDecreasingExp.getLocation() != null) {
                loc = (Location) myOperationDecreasingExp.getLocation().clone();
            }
            else {
                loc = (Location) stmt.getLocation().clone();
            }
            loc.setDetails("Show Termination of Recursive Call");
            Utilities.setLocation(exp, loc);
            ConfirmStmt conf = new ConfirmStmt(loc, exp, false);

            // Add it to our list of assertions
            myCurrentAssertiveCode.addCode(conf);
        }

        // Get the requires clause for this operation
        Exp requires;
        boolean simplify = false;
        if (opDec.getRequires() != null) {
            requires = Exp.copy(opDec.getRequires());

            // Simplify if we just have true
            if (requires.isLiteralTrue()) {
                simplify = true;
            }
        }
        else {
            requires = myTypeGraph.getTrueVarExp();
            simplify = true;
        }

        // Find all the replacements that needs to happen to the requires
        // and ensures clauses
        List<ProgramExp> callArgs = stmt.getArguments();
        List<Exp> replaceArgs = modifyArgumentList(callArgs);

        // Modify ensures using the parameter modes
        ensures =
                modifyEnsuresByParameter(ensures, stmt.getLocation(), opDec
                        .getName().getName(), opDec.getParameters(), isLocal);

        // Replace PreCondition variables in the requires clause
        requires =
                replaceFormalWithActualReq(requires, opDec.getParameters(),
                        replaceArgs);

        // Replace PostCondition variables in the ensures clause
        ensures =
                replaceFormalWithActualEns(ensures, opDec.getParameters(),
                        opDec.getStateVars(), replaceArgs, false);

        // Replace facility actuals variables in the requires clause
        requires =
                Utilities.replaceFacilityFormalWithActual(stmt.getLocation(),
                        requires, opDec.getParameters(),
                        myInstantiatedFacilityArgMap, myCurrentModuleScope);

        // Replace facility actuals variables in the ensures clause
        ensures =
                Utilities.replaceFacilityFormalWithActual(stmt.getLocation(),
                        ensures, opDec.getParameters(),
                        myInstantiatedFacilityArgMap, myCurrentModuleScope);

        // NY YS
        // Duration for CallStmt
        if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)) {
            Location loc = (Location) stmt.getLocation().clone();
            ConfirmStmt finalConfirm = myCurrentAssertiveCode.getFinalConfirm();
            Exp finalConfirmExp = finalConfirm.getAssertion();

            // Obtain the corresponding OperationProfileEntry
            OperationProfileEntry ope =
                    Utilities.searchOperationProfile(loc, stmt.getQualifier(),
                            stmt.getName(), argTypes, myCurrentModuleScope);

            // Add the profile ensures as additional assume
            Exp profileEnsures = ope.getEnsuresClause();
            if (profileEnsures != null) {
                profileEnsures =
                        replaceFormalWithActualEns(profileEnsures, opDec
                                .getParameters(), opDec.getStateVars(),
                                replaceArgs, false);

                // Obtain the current location
                if (stmt.getName().getLocation() != null) {
                    // Set the details of the current location
                    Location ensuresLoc = (Location) loc.clone();
                    ensuresLoc.setDetails("Ensures Clause of "
                            + opDec.getName() + " from Profile "
                            + ope.getName());
                    Utilities.setLocation(profileEnsures, ensuresLoc);
                }

                ensures = myTypeGraph.formConjunct(ensures, profileEnsures);
            }

            // Construct the Duration Clause
            Exp opDur = Exp.copy(ope.getDurationClause());

            // Replace PostCondition variables in the duration clause
            opDur =
                    replaceFormalWithActualEns(opDur, opDec.getParameters(),
                            opDec.getStateVars(), replaceArgs, false);

            VarExp cumDur =
                    Utilities.createVarExp((Location) loc.clone(), null,
                            Utilities.createPosSymbol(Utilities
                                    .getCumDur(finalConfirmExp)),
                            myTypeGraph.R, null);
            Exp durCallExp =
                    Utilities.createDurCallExp((Location) loc.clone(), Integer
                            .toString(opDec.getParameters().size()), Z,
                            myTypeGraph.R);
            InfixExp sumEvalDur =
                    new InfixExp((Location) loc.clone(), opDur, Utilities
                            .createPosSymbol("+"), durCallExp);
            sumEvalDur.setMathType(myTypeGraph.R);
            sumEvalDur =
                    new InfixExp((Location) loc.clone(), Exp.copy(cumDur),
                            Utilities.createPosSymbol("+"), sumEvalDur);
            sumEvalDur.setMathType(myTypeGraph.R);

            // For any evaluates mode expression, we need to finalize the variable
            edu.clemson.cs.r2jt.collections.List<ProgramExp> assignExpList =
                    stmt.getArguments();
            for (int i = 0; i < assignExpList.size(); i++) {
                ParameterVarDec p = opDec.getParameters().get(i);
                VariableExp pExp = (VariableExp) assignExpList.get(i);
                if (p.getMode() == Mode.EVALUATES) {
                    VarDec v =
                            new VarDec(Utilities.getVarName(pExp), p.getTy());
                    FunctionExp finalDur =
                            Utilities.createFinalizAnyDur(v, myTypeGraph.R);
                    sumEvalDur =
                            new InfixExp((Location) loc.clone(), sumEvalDur,
                                    Utilities.createPosSymbol("+"), finalDur);
                    sumEvalDur.setMathType(myTypeGraph.R);
                }
            }

            // Replace Cum_Dur in our final ensures clause
            finalConfirmExp =
                    Utilities.replace(finalConfirmExp, cumDur, sumEvalDur);
            myCurrentAssertiveCode.setFinalConfirm(finalConfirmExp,
                    finalConfirm.getSimplify());
        }

        // Modify the location of the requires clause and add it to myCurrentAssertiveCode
        if (requires != null) {
            // Obtain the current location
            // Note: If we don't have a location, we create one
            Location loc;
            if (stmt.getName().getLocation() != null) {
                loc = (Location) stmt.getName().getLocation().clone();
            }
            else {
                loc = new Location(null, null);
            }

            // Append the name of the current procedure
            String details = "";
            if (myCurrentOperationEntry != null) {
                details = " in Procedure " + myCurrentOperationEntry.getName();
            }

            // Set the details of the current location
            loc.setDetails("Requires Clause of " + opDec.getName() + details);
            Utilities.setLocation(requires, loc);

            // Add this to our list of things to confirm
            myCurrentAssertiveCode.addConfirm((Location) loc.clone(), requires,
                    simplify);
        }

        // Modify the location of the requires clause and add it to myCurrentAssertiveCode
        if (ensures != null) {
            // Obtain the current location
            Location loc = null;
            if (stmt.getName().getLocation() != null) {
                // Set the details of the current location
                loc = (Location) stmt.getName().getLocation().clone();
                loc.setDetails("Ensures Clause of " + opDec.getName());
                Utilities.setLocation(ensures, loc);
            }

            // Add this to our list of things to assume
            myCurrentAssertiveCode.addAssume(loc, ensures, false);
        }

        // Verbose Mode Debug Messages
        myVCBuffer.append("\nOperation Call Rule Applied: \n");
        myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
        myVCBuffer.append("\n_____________________ \n");
    }

    /**
     * <p>Applies different rules to code statements.</p>
     *
     * @param statement The different statements.
     */
    private void applyCodeRules(Statement statement) {
        // Apply each statement rule here.
        if (statement instanceof AssumeStmt) {
            applyAssumeStmtRule((AssumeStmt) statement);
        }
        else if (statement instanceof CallStmt) {
            applyCallStmtRule((CallStmt) statement);
        }
        else if (statement instanceof ConfirmStmt) {
            applyConfirmStmtRule((ConfirmStmt) statement);
        }
        else if (statement instanceof FuncAssignStmt) {
            applyFuncAssignStmtRule((FuncAssignStmt) statement);
        }
        else if (statement instanceof IfStmt) {
            applyIfStmtRule((IfStmt) statement);
        }
        else if (statement instanceof MemoryStmt) {
            // TODO: Deal with Forget
            if (((MemoryStmt) statement).isRemember()) {
                applyRememberRule();
            }
        }
        else if (statement instanceof PresumeStmt) {
            applyPresumeStmtRule((PresumeStmt) statement);
        }
        else if (statement instanceof SwapStmt) {
            applySwapStmtRule((SwapStmt) statement);
        }
        else if (statement instanceof WhileStmt) {
            applyWhileStmtRule((WhileStmt) statement);
        }
    }

    /**
     * <p>Applies the confirm rule to the
     * <code>Statement</code>.</p>
     *
     * @param stmt Our current <code>ConfirmStmt</code>.
     */
    private void applyConfirmStmtRule(ConfirmStmt stmt) {
        // Check to see if our assertion can be simplified
        Exp assertion = stmt.getAssertion();
        if (stmt.getSimplify()) {
            // Verbose Mode Debug Messages
            myVCBuffer.append("\nConfirm Rule Applied and Simplified: \n");
            myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
            myVCBuffer.append("\n_____________________ \n");
        }
        else {
            // Obtain the current final confirm statement
            ConfirmStmt currentFinalConfirm =
                    myCurrentAssertiveCode.getFinalConfirm();

            // Check to see if we can simplify the final confirm
            if (currentFinalConfirm.getSimplify()) {
                // Obtain the current location
                if (assertion.getLocation() != null) {
                    // Set the details of the current location
                    Location loc = (Location) assertion.getLocation().clone();
                    Utilities.setLocation(assertion, loc);
                }

                myCurrentAssertiveCode.setFinalConfirm(assertion, stmt
                        .getSimplify());

                // Verbose Mode Debug Messages
                myVCBuffer.append("\nConfirm Rule Applied and Simplified: \n");
                myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
                myVCBuffer.append("\n_____________________ \n");
            }
            else {
                // Create a new and expression
                InfixExp newConf =
                        myTypeGraph.formConjunct(assertion, currentFinalConfirm
                                .getAssertion());

                // Set this new expression as the new final confirm
                myCurrentAssertiveCode.setFinalConfirm(newConf, false);

                // Verbose Mode Debug Messages
                myVCBuffer.append("\nConfirm Rule Applied: \n");
                myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
                myVCBuffer.append("\n_____________________ \n");
            }
        }
    }

    /**
     * <p>Applies the correspondence rule.</p>
     *
     * @param dec Representation declaration object.
     */
    private void applyCorrespondenceRule(RepresentationDec dec) {
        // Create a new assertive code to hold the correspondence VCs
        AssertiveCode assertiveCode =
                new AssertiveCode(myInstanceEnvironment, dec);

        // Obtain the location for each assume clause
        Location decLoc = dec.getLocation();

        // Add the global constraints as given
        Location constraintLoc;
        if (myGlobalConstraintExp.getLocation() != null) {
            constraintLoc =
                    (Location) myGlobalConstraintExp.getLocation().clone();
        }
        else {
            constraintLoc = (Location) decLoc.clone();
        }
        constraintLoc.setDetails("Global Constraints from "
                + myCurrentModuleScope.getModuleIdentifier());
        assertiveCode.addAssume(constraintLoc, myGlobalConstraintExp, false);

        // Add the global require clause as given
        assertiveCode.addAssume((Location) decLoc.clone(), myGlobalRequiresExp,
                false);

        // Add the convention as given
        assertiveCode.addAssume((Location) decLoc.clone(), dec.getConvention(),
                false);

        // Add the type representation constraint
        Exp repConstraintExp = null;
        Set<VarExp> keys = myRepresentationConstraintMap.keySet();
        for (VarExp varExp : keys) {
            if (varExp.getQualifier() == null
                    && varExp.getName().getName().equals(
                            dec.getName().getName())) {
                if (repConstraintExp == null) {
                    repConstraintExp =
                            myRepresentationConstraintMap.get(varExp);
                }
                else {
                    Utilities.ambiguousTy(dec.getRepresentation(), dec
                            .getLocation());
                }
            }
        }
        assertiveCode.addAssume((Location) decLoc.clone(), repConstraintExp,
                false);

        // Add the correspondence as given
        Exp correspondenceExp = Exp.copy(dec.getCorrespondence());
        assertiveCode.addAssume((Location) decLoc.clone(), correspondenceExp,
                false);

        // Store the correspondence in our map
        myRepresentationCorrespondenceMap.put(Utilities.createVarExp(decLoc,
                null, dec.getName(),
                dec.getRepresentation().getMathTypeValue(), null), Exp
                .copy(correspondenceExp));

        // Search for the type we are implementing
        SymbolTableEntry ste =
                Utilities.searchProgramType(dec.getLocation(), null, dec
                        .getName(), myCurrentModuleScope);

        ProgramTypeEntry typeEntry;
        if (ste instanceof ProgramTypeEntry) {
            typeEntry = ste.toProgramTypeEntry(dec.getLocation());
        }
        else {
            typeEntry =
                    ste.toRepresentationTypeEntry(dec.getLocation())
                            .getDefiningTypeEntry();
        }

        // Make sure we don't have a generic type
        if (typeEntry.getDefiningElement() instanceof TypeDec) {
            // Obtain the original dec from the AST
            TypeDec type = (TypeDec) typeEntry.getDefiningElement();

            // Create a variable expression from the type exemplar
            VarExp exemplar =
                    Utilities.createVarExp(type.getLocation(), null, type
                            .getExemplar(), typeEntry.getModelType(), null);

            DotExp conceptualVar =
                    Utilities.createConcVarExp(null, exemplar, typeEntry
                            .getModelType(), BOOLEAN);

            // Make sure we have a constraint
            Exp constraint;
            if (type.getConstraint() == null) {
                constraint = myTypeGraph.getTrueVarExp();
            }
            else {
                constraint = Exp.copy(type.getConstraint());
            }
            constraint = Utilities.replace(constraint, exemplar, conceptualVar);

            // Set the location for the constraint
            Location loc;
            if (correspondenceExp.getLocation() != null) {
                loc = (Location) correspondenceExp.getLocation().clone();
            }
            else {
                loc = (Location) type.getLocation().clone();
            }
            loc.setDetails("Well Defined Correspondence for "
                    + dec.getName().getName());
            Utilities.setLocation(constraint, loc);

            // We need to make sure the constraints for the type we are
            // implementing is met.
            boolean simplify = false;
            // Simplify if we just have true
            if (constraint.isLiteralTrue()) {
                simplify = true;
            }
            assertiveCode.setFinalConfirm(constraint, simplify);
        }

        // Add this new assertive code to our incomplete assertive code stack
        myIncAssertiveCodeStack.push(assertiveCode);

        // Verbose Mode Debug Messages
        String newString =
                "\n========================= Type Representation Name:\t"
                        + dec.getName().getName()
                        + " =========================\n";
        newString += "\nCorrespondence Rule Applied: \n";
        newString += assertiveCode.assertionToString();
        newString += "\n_____________________ \n";
        myIncAssertiveCodeStackInfo.push(newString);
    }

    /**
     * <p>Applies the facility declaration rule.</p>
     *
     * @param dec Facility declaration object.
     * @param addToIncAssertiveCodeStack True if the created assertive code needs
     *                                   to be added to our incomplete assertive code stack.
     */
    private void applyFacilityDeclRule(FacilityDec dec,
            boolean addToIncAssertiveCodeStack) {
        // Create a new assertive code to hold the facility declaration VCs
        AssertiveCode assertiveCode =
                new AssertiveCode(myInstanceEnvironment, dec);

        // Location for the current facility dec
        Location decLoc = dec.getLocation();

        // Add the global constraints as given (if any)
        if (myGlobalConstraintExp != null) {
            Location gConstraintLoc;
            if (myGlobalConstraintExp.getLocation() != null) {
                gConstraintLoc =
                        (Location) myGlobalConstraintExp.getLocation().clone();
            }
            else {
                gConstraintLoc = (Location) decLoc.clone();
            }
            gConstraintLoc.setDetails("Global Constraints from "
                    + myCurrentModuleScope.getModuleIdentifier());
            assertiveCode.addAssume(gConstraintLoc, myGlobalConstraintExp,
                    false);
        }

        // Add the global require clause as given (if any)
        if (myGlobalRequiresExp != null) {
            Location gRequiresLoc;
            if (myGlobalRequiresExp.getLocation() != null) {
                gRequiresLoc =
                        (Location) myGlobalRequiresExp.getLocation().clone();
            }
            else {
                gRequiresLoc = (Location) decLoc.clone();
            }
            gRequiresLoc.setDetails("Global Requires Clause from "
                    + myCurrentModuleScope.getModuleIdentifier());
            assertiveCode.addAssume(gRequiresLoc, myGlobalRequiresExp, false);
        }

        // Add a remember rule
        assertiveCode.addCode(new MemoryStmt((Location) decLoc.clone(), true));

        try {
            // Obtain the concept module for the facility
            ConceptModuleDec facConceptDec =
                    (ConceptModuleDec) mySymbolTable
                            .getModuleScope(
                                    new ModuleIdentifier(dec.getConceptName()
                                            .getName())).getDefiningElement();

            // Convert the module arguments into mathematical expressions
            // Note that we could potentially have a nested function call
            // as one of the arguments, therefore we pass in the assertive
            // code to store the confirm statement generated from all the
            // requires clauses.
            List<Exp> conceptFormalArgList =
                    createModuleFormalArgExpList(facConceptDec.getParameters());
            List<Exp> conceptActualArgList =
                    createModuleActualArgExpList(assertiveCode, dec
                            .getConceptParams());

            // Facility Decl Rule (Concept Requires): CPC[ n ~> n_exp, R ~> IR ]
            Exp conceptReq =
                    replaceFacilityDeclarationVariables(getRequiresClause(
                            facConceptDec.getLocation(), facConceptDec),
                            conceptFormalArgList, conceptActualArgList);

            if (!conceptReq.equals(myTypeGraph.getTrueVarExp())) {
                Location conceptReqLoc =
                        (Location) dec.getConceptName().getLocation().clone();
                conceptReqLoc.setDetails("Requires Clause for "
                        + dec.getConceptName().getName()
                        + " in Facility Instantiation Rule");
                conceptReq.setLocation(conceptReqLoc);
                assertiveCode.addConfirm(conceptReqLoc, conceptReq, false);
            }

            // Create a mapping from concept formal to actual arguments
            // for future use.
            Map<Exp, Exp> conceptArgMap = new HashMap<Exp, Exp>();
            for (int i = 0; i < conceptFormalArgList.size(); i++) {
                conceptArgMap.put(conceptFormalArgList.get(i),
                        conceptActualArgList.get(i));
            }

            // Facility Decl Rule (Concept Realization Requires):
            //      (RPC[ rn ~> rn_exp, RR ~> IRR ])[ n ~> n_exp, R ~> IR ]
            //
            // Note: Only apply this part of the rule if the concept realization
            // is not externally realized.
            Map<Exp, Exp> conceptRealizArgMap = new HashMap<Exp, Exp>();
            if (!dec.getExternallyRealizedFlag()) {
                ConceptBodyModuleDec facConceptRealizDec =
                        (ConceptBodyModuleDec) mySymbolTable.getModuleScope(
                                new ModuleIdentifier(dec.getBodyName()
                                        .getName())).getDefiningElement();

                // Convert the module arguments into mathematical expressions
                // Note that we could potentially have a nested function call
                // as one of the arguments, therefore we pass in the assertive
                // code to store the confirm statement generated from all the
                // requires clauses.
                List<Exp> conceptRealizFormalArgList =
                        createModuleFormalArgExpList(facConceptRealizDec
                                .getParameters());
                List<Exp> conceptRealizActualArgList =
                        createModuleActualArgExpList(assertiveCode, dec
                                .getBodyParams());

                // 1) Replace the concept realization formal with actuals
                Exp conceptRealizReq =
                        replaceFacilityDeclarationVariables(getRequiresClause(
                                facConceptRealizDec.getLocation(),
                                facConceptRealizDec),
                                conceptRealizFormalArgList,
                                conceptRealizActualArgList);

                // 2) Replace the concept formal with actuals
                conceptRealizReq =
                        replaceFacilityDeclarationVariables(conceptRealizReq,
                                conceptFormalArgList, conceptActualArgList);

                // Add this as a new confirm statement in our assertive code
                if (!conceptRealizReq.equals(myTypeGraph.getTrueVarExp())) {
                    Location conceptRealizReqLoc =
                            (Location) dec.getBodyName().getLocation().clone();
                    conceptRealizReqLoc.setDetails("Requires Clause for "
                            + dec.getBodyName().getName()
                            + " in Facility Instantiation Rule");
                    conceptRealizReq.setLocation(conceptRealizReqLoc);
                    assertiveCode.addConfirm(conceptRealizReqLoc,
                            conceptRealizReq, false);
                }

                // Create a mapping from concept realization formal to actual arguments
                // for future use.
                for (int i = 0; i < conceptRealizFormalArgList.size(); i++) {
                    conceptRealizArgMap.put(conceptRealizFormalArgList.get(i),
                            conceptRealizActualArgList.get(i));
                }

                // Facility Decl Rule (Operations as Concept Realization Parameters):
                // preRP [ rn ~> rn_exp, rx ~> irx ] implies preIRP and
                // postIRP implies postRP [ rn ~> rn_exp, #rx ~> #irx, rx ~> irx ]
                //
                // Note: We need to pass in empty lists for enhancement/enhancement realization
                // formal and actuals, because they are not needed here.
                assertiveCode =
                        facilityDeclOperationParamHelper(decLoc, assertiveCode,
                                facConceptRealizDec.getParameters(), dec
                                        .getBodyParams(), conceptFormalArgList,
                                conceptActualArgList,
                                conceptRealizFormalArgList,
                                conceptRealizActualArgList,
                                new ArrayList<Exp>(), new ArrayList<Exp>(),
                                new ArrayList<Exp>(), new ArrayList<Exp>());
            }

            // TODO: Figure out how to apply the rule when there are enhancements for concept realizations
            List<EnhancementItem> enhancementList = dec.getEnhancements();
            for (EnhancementItem e : enhancementList) {
                // Do something here.
            }

            // Apply the facility declaration rules to regular enhancement/enhancement realizations
            List<EnhancementBodyItem> enhancementBodyList =
                    dec.getEnhancementBodies();
            Map<PosSymbol, Map<Exp, Exp>> enhancementArgMaps =
                    new HashMap<PosSymbol, Map<Exp, Exp>>();
            for (EnhancementBodyItem ebi : enhancementBodyList) {
                // Obtain the enhancement module for the facility
                EnhancementModuleDec facEnhancementDec =
                        (EnhancementModuleDec) mySymbolTable.getModuleScope(
                                new ModuleIdentifier(ebi.getName().getName()))
                                .getDefiningElement();

                // Convert the module arguments into mathematical expressions
                // Note that we could potentially have a nested function call
                // as one of the arguments, therefore we pass in the assertive
                // code to store the confirm statement generated from all the
                // requires clauses.
                List<Exp> enhancementFormalArgList =
                        createModuleFormalArgExpList(facEnhancementDec
                                .getParameters());
                List<Exp> enhancementActualArgList =
                        createModuleActualArgExpList(assertiveCode, ebi
                                .getParams());

                // Facility Decl Rule (Enhancement Requires):
                // CPC[ n ~> n_exp, R ~> IR ] (Use the enhancement equivalents)
                Exp enhancementReq =
                        replaceFacilityDeclarationVariables(getRequiresClause(
                                facEnhancementDec.getLocation(),
                                facEnhancementDec), enhancementFormalArgList,
                                enhancementActualArgList);

                if (!enhancementReq.equals(myTypeGraph.getTrueVarExp())) {
                    Location enhancementReqLoc =
                            (Location) ebi.getName().getLocation().clone();
                    enhancementReqLoc.setDetails("Requires Clause for "
                            + ebi.getName().getName()
                            + " in Facility Instantiation Rule");
                    enhancementReq.setLocation(enhancementReqLoc);
                    assertiveCode.addConfirm(enhancementReqLoc, enhancementReq,
                            false);
                }

                // Create a mapping from concept formal to actual arguments
                // for future use.
                Map<Exp, Exp> enhancementArgMap = new HashMap<Exp, Exp>();
                for (int i = 0; i < enhancementFormalArgList.size(); i++) {
                    enhancementArgMap.put(enhancementFormalArgList.get(i),
                            enhancementActualArgList.get(i));
                }
                enhancementArgMaps.put(facEnhancementDec.getName(),
                        enhancementArgMap);

                // Facility Decl Rule (Enhancement Realization Requires):
                //      (RPC[ rn ~> rn_exp, RR ~> IRR ])[ n ~> n_exp, R ~> IR ]
                //          (Use the enhancement realization equivalents and
                //           also have to replace enhancement formals with actuals)
                //
                // Note: Only apply this part of the rule if the concept realization
                // is not externally realized.
                Map<Exp, Exp> enhancementRealizArgMap = new HashMap<Exp, Exp>();
                EnhancementBodyModuleDec facEnhancementRealizDec =
                        (EnhancementBodyModuleDec) mySymbolTable
                                .getModuleScope(
                                        new ModuleIdentifier(ebi.getBodyName()
                                                .getName()))
                                .getDefiningElement();

                // Convert the module arguments into mathematical expressions
                // Note that we could potentially have a nested function call
                // as one of the arguments, therefore we pass in the assertive
                // code to store the confirm statement generated from all the
                // requires clauses.
                List<Exp> enhancementRealizFormalArgList =
                        createModuleFormalArgExpList(facEnhancementRealizDec
                                .getParameters());
                List<Exp> enhancementRealizActualArgList =
                        createModuleActualArgExpList(assertiveCode, ebi
                                .getBodyParams());

                // 1) Replace the enhancement realization formal with actuals
                Exp enhancementRealizReq =
                        replaceFacilityDeclarationVariables(getRequiresClause(
                                facEnhancementRealizDec.getLocation(),
                                facEnhancementRealizDec),
                                enhancementRealizFormalArgList,
                                enhancementRealizActualArgList);

                // 2) Replace the concept formal with actuals
                enhancementRealizReq =
                        replaceFacilityDeclarationVariables(
                                enhancementRealizReq, conceptFormalArgList,
                                conceptActualArgList);

                // 3) Replace the enhancement formal with actuals
                enhancementRealizReq =
                        replaceFacilityDeclarationVariables(
                                enhancementRealizReq, enhancementFormalArgList,
                                enhancementActualArgList);

                // Add this as a new confirm statement in our assertive code
                if (!enhancementRealizReq.equals(myTypeGraph.getTrueVarExp())) {
                    Location enhancementRealizReqLoc =
                            (Location) ebi.getBodyName().getLocation().clone();
                    enhancementRealizReqLoc.setDetails("Requires Clause for "
                            + ebi.getBodyName().getName()
                            + " in Facility Instantiation Rule");
                    enhancementRealizReq.setLocation(enhancementRealizReqLoc);
                    assertiveCode.addConfirm(enhancementRealizReqLoc,
                            enhancementRealizReq, false);
                }

                // Create a mapping from enhancement realization formal to actual arguments
                // for future use.
                for (int i = 0; i < enhancementRealizFormalArgList.size(); i++) {
                    enhancementRealizArgMap.put(enhancementRealizFormalArgList
                            .get(i), enhancementRealizActualArgList.get(i));
                }
                enhancementArgMaps.put(facEnhancementRealizDec.getName(),
                        enhancementRealizArgMap);

                // Facility Decl Rule (Operations as Enhancement Realization Parameters):
                // preRP [ rn ~> rn_exp, rx ~> irx ] implies preIRP and
                // postIRP implies postRP [ rn ~> rn_exp, #rx ~> #irx, rx ~> irx ]
                //
                // Note: We need to pass in empty lists for concept realization
                // formal and actuals, because they are not needed here.
                assertiveCode =
                        facilityDeclOperationParamHelper(decLoc, assertiveCode,
                                facEnhancementRealizDec.getParameters(), ebi
                                        .getBodyParams(), conceptFormalArgList,
                                conceptActualArgList, new ArrayList<Exp>(),
                                new ArrayList<Exp>(), enhancementFormalArgList,
                                enhancementActualArgList,
                                enhancementRealizFormalArgList,
                                enhancementRealizActualArgList);
            }

            // The code below stores a mapping between each of the concept/realization/enhancement
            // formal arguments to the actual arguments instantiated by the facility.
            // This is needed to replace the requires/ensures clauses from facility instantiated
            // operations.
            FacilityFormalToActuals formalToActuals =
                    new FacilityFormalToActuals(conceptArgMap,
                            conceptRealizArgMap, enhancementArgMaps);
            for (Dec d : facConceptDec.getDecs()) {
                if (d instanceof TypeDec) {
                    Location loc = (Location) dec.getLocation().clone();
                    PosSymbol qual = dec.getName().copy();
                    PosSymbol name = d.getName().copy();
                    Ty dTy = ((TypeDec) d).getModel();
                    myInstantiatedFacilityArgMap.put(Utilities.createVarExp(
                            loc, qual, name, dTy.getMathType(), dTy
                                    .getMathTypeValue()), formalToActuals);
                }
            }
        }
        catch (NoSuchSymbolException e) {
            Utilities.noSuchModule(dec.getLocation());
        }

        // This is a local facility and we need to add it to our incomplete
        // assertive code stack.
        if (addToIncAssertiveCodeStack) {
            // Add this new assertive code to our incomplete assertive code stack
            myIncAssertiveCodeStack.push(assertiveCode);

            // Verbose Mode Debug Messages
            String newString =
                    "\n========================= Facility Dec Name:\t"
                            + dec.getName().getName()
                            + " =========================\n";
            newString += "\nFacility Declaration Rule Applied: \n";
            newString += assertiveCode.assertionToString();
            newString += "\n_____________________ \n";
            myIncAssertiveCodeStackInfo.push(newString);
        }
    }

    /**
     * <p>Applies the function assignment rule to the
     * <code>Statement</code>.</p>
     *
     * @param stmt Our current <code>FuncAssignStmt</code>.
     */
    private void applyFuncAssignStmtRule(FuncAssignStmt stmt) {
        PosSymbol qualifier = null;
        ProgramExp assignExp = stmt.getAssign();
        ProgramParamExp assignParamExp = null;

        // Replace all instances of the variable on the left hand side
        // in the ensures clause with the expression on the right.
        Exp leftVariable;

        // We have a variable inside a record as the variable being assigned.
        if (stmt.getVar() instanceof VariableDotExp) {
            VariableDotExp v = (VariableDotExp) stmt.getVar();
            List<VariableExp> vList = v.getSegments();
            edu.clemson.cs.r2jt.collections.List<Exp> newSegments =
                    new edu.clemson.cs.r2jt.collections.List<Exp>();

            // Loot through each variable expression and add it to our dot list
            for (VariableExp vr : vList) {
                VarExp varExp = new VarExp();
                if (vr instanceof VariableNameExp) {
                    varExp.setName(((VariableNameExp) vr).getName());
                    varExp.setMathType(vr.getMathType());
                    varExp.setMathTypeValue(vr.getMathTypeValue());
                    newSegments.add(varExp);
                }
            }

            // Expression to be replaced
            leftVariable = new DotExp(v.getLocation(), newSegments, null);
            leftVariable.setMathType(v.getMathType());
            leftVariable.setMathTypeValue(v.getMathTypeValue());
        }
        // We have a regular variable being assigned.
        else {
            // Expression to be replaced
            VariableNameExp v = (VariableNameExp) stmt.getVar();
            leftVariable = new VarExp(v.getLocation(), null, v.getName());
            leftVariable.setMathType(v.getMathType());
            leftVariable.setMathTypeValue(v.getMathTypeValue());
        }

        // Simply replace the numbers/characters/strings
        if (assignExp instanceof ProgramIntegerExp
                || assignExp instanceof ProgramCharExp
                || assignExp instanceof ProgramStringExp) {
            Exp replaceExp =
                    Utilities.convertExp(assignExp, myCurrentModuleScope);

            // Replace all instances of the left hand side
            // variable in the current final confirm statement.
            ConfirmStmt confirmStmt = myCurrentAssertiveCode.getFinalConfirm();
            Exp newConf = confirmStmt.getAssertion();
            newConf = Utilities.replace(newConf, leftVariable, replaceExp);

            // Set this as our new final confirm statement.
            myCurrentAssertiveCode.setFinalConfirm(newConf, confirmStmt
                    .getSimplify());
        }
        else {
            // Check to see what kind of expression is on the right hand side
            if (assignExp instanceof ProgramParamExp) {
                // Cast to a ProgramParamExp
                assignParamExp = (ProgramParamExp) assignExp;
            }
            else if (assignExp instanceof ProgramDotExp) {
                // Cast to a ProgramParamExp
                ProgramDotExp dotExp = (ProgramDotExp) assignExp;
                assignParamExp = (ProgramParamExp) dotExp.getExp();
                qualifier = dotExp.getQualifier();
            }

            // Call a method to locate the operation dec for this call
            List<PTType> argTypes = new LinkedList<PTType>();
            for (ProgramExp arg : assignParamExp.getArguments()) {
                argTypes.add(arg.getProgramType());
            }
            OperationEntry opEntry =
                    Utilities.searchOperation(stmt.getLocation(), qualifier,
                            assignParamExp.getName(), argTypes,
                            myCurrentModuleScope);
            OperationDec opDec = Utilities.convertToOperationDec(opEntry);

            // Check for recursive call of itself
            if (myCurrentOperationEntry != null
                    && myOperationDecreasingExp != null
                    && myCurrentOperationEntry.getName().equals(
                            opEntry.getName())
                    && myCurrentOperationEntry.getReturnType().equals(
                            opEntry.getReturnType())
                    && myCurrentOperationEntry.getSourceModuleIdentifier()
                            .equals(opEntry.getSourceModuleIdentifier())) {
                // Create a new confirm statement using P_val and the decreasing clause
                VarExp pVal =
                        Utilities.createPValExp(myOperationDecreasingExp
                                .getLocation(), myCurrentModuleScope);

                // Create a new infix expression
                IntegerExp oneExp = new IntegerExp();
                oneExp.setValue(1);
                oneExp.setMathType(myOperationDecreasingExp.getMathType());
                InfixExp leftExp =
                        new InfixExp(stmt.getLocation(), oneExp, Utilities
                                .createPosSymbol("+"), Exp
                                .copy(myOperationDecreasingExp));
                leftExp.setMathType(myOperationDecreasingExp.getMathType());
                InfixExp exp =
                        Utilities.createLessThanEqExp(stmt.getLocation(),
                                leftExp, pVal, BOOLEAN);

                // Create the new confirm statement
                Location loc;
                if (myOperationDecreasingExp.getLocation() != null) {
                    loc =
                            (Location) myOperationDecreasingExp.getLocation()
                                    .clone();
                }
                else {
                    loc = (Location) stmt.getLocation().clone();
                }
                loc.setDetails("Show Termination of Recursive Call");
                Utilities.setLocation(exp, loc);
                ConfirmStmt conf = new ConfirmStmt(loc, exp, false);

                // Add it to our list of assertions
                myCurrentAssertiveCode.addCode(conf);
            }

            // Get the requires clause for this operation
            Exp requires;
            boolean simplify = false;
            if (opDec.getRequires() != null) {
                requires = Exp.copy(opDec.getRequires());

                // Simplify if we just have true
                if (requires.isLiteralTrue()) {
                    simplify = true;
                }
            }
            else {
                requires = myTypeGraph.getTrueVarExp();
                simplify = true;
            }

            // Find all the replacements that needs to happen to the requires
            // and ensures clauses
            List<ProgramExp> callArgs = assignParamExp.getArguments();
            List<Exp> replaceArgs = modifyArgumentList(callArgs);

            // Replace PreCondition variables in the requires clause
            requires =
                    replaceFormalWithActualReq(requires, opDec.getParameters(),
                            replaceArgs);

            // Replace facility actuals variables in the requires clause
            requires =
                    Utilities.replaceFacilityFormalWithActual(assignParamExp
                            .getLocation(), requires, opDec.getParameters(),
                            myInstantiatedFacilityArgMap, myCurrentModuleScope);

            // Modify the location of the requires clause and add it to myCurrentAssertiveCode
            // Obtain the current location
            // Note: If we don't have a location, we create one
            Location reqloc;
            if (assignParamExp.getName().getLocation() != null) {
                reqloc =
                        (Location) assignParamExp.getName().getLocation()
                                .clone();
            }
            else {
                reqloc = new Location(null, null);
            }

            // Append the name of the current procedure
            String details = "";
            if (myCurrentOperationEntry != null) {
                details = " in Procedure " + myCurrentOperationEntry.getName();
            }

            // Set the details of the current location
            reqloc
                    .setDetails("Requires Clause of " + opDec.getName()
                            + details);
            Utilities.setLocation(requires, reqloc);

            // Add this to our list of things to confirm
            myCurrentAssertiveCode.addConfirm((Location) reqloc.clone(),
                    requires, simplify);

            // Get the ensures clause for this operation
            // Note: If there isn't an ensures clause, it is set to "True"
            Exp ensures, opEnsures;
            if (opDec.getEnsures() != null) {
                opEnsures = Exp.copy(opDec.getEnsures());

                // Make sure we have an EqualsExp, else it is an error.
                if (opEnsures instanceof EqualsExp) {
                    // Has to be a VarExp on the left hand side (containing the name
                    // of the function operation)
                    if (((EqualsExp) opEnsures).getLeft() instanceof VarExp) {
                        VarExp leftExp =
                                (VarExp) ((EqualsExp) opEnsures).getLeft();

                        // Check if it has the name of the operation
                        if (leftExp.getName().equals(opDec.getName())) {
                            ensures = ((EqualsExp) opEnsures).getRight();

                            // Obtain the current location
                            if (assignParamExp.getName().getLocation() != null) {
                                // Set the details of the current location
                                Location loc =
                                        (Location) assignParamExp.getName()
                                                .getLocation().clone();
                                loc.setDetails("Ensures Clause of "
                                        + opDec.getName());
                                Utilities.setLocation(ensures, loc);
                            }

                            // Replace the formal with the actual
                            ensures =
                                    replaceFormalWithActualEns(ensures, opDec
                                            .getParameters(), opDec
                                            .getStateVars(), replaceArgs, true);

                            // Replace facility actuals variables in the ensures clause
                            ensures =
                                    Utilities.replaceFacilityFormalWithActual(
                                            assignParamExp.getLocation(),
                                            ensures, opDec.getParameters(),
                                            myInstantiatedFacilityArgMap,
                                            myCurrentModuleScope);

                            // Replace all instances of the left hand side
                            // variable in the current final confirm statement.
                            ConfirmStmt confirmStmt =
                                    myCurrentAssertiveCode.getFinalConfirm();
                            Exp newConf = confirmStmt.getAssertion();
                            newConf =
                                    Utilities.replace(newConf, leftVariable,
                                            ensures);

                            // Set this as our new final confirm statement.
                            myCurrentAssertiveCode.setFinalConfirm(newConf,
                                    confirmStmt.getSimplify());

                            // NY YS
                            // Duration for CallStmt
                            if (myInstanceEnvironment.flags
                                    .isFlagSet(FLAG_ALTPVCS_VC)) {
                                Location loc =
                                        (Location) stmt.getLocation().clone();
                                ConfirmStmt finalConfirm =
                                        myCurrentAssertiveCode
                                                .getFinalConfirm();
                                Exp finalConfirmExp =
                                        finalConfirm.getAssertion();

                                // Obtain the corresponding OperationProfileEntry
                                OperationProfileEntry ope =
                                        Utilities.searchOperationProfile(loc,
                                                qualifier, assignParamExp
                                                        .getName(), argTypes,
                                                myCurrentModuleScope);

                                // Add the profile ensures as additional assume
                                Exp profileEnsures = ope.getEnsuresClause();
                                if (profileEnsures != null) {
                                    profileEnsures =
                                            replaceFormalWithActualEns(
                                                    profileEnsures, opDec
                                                            .getParameters(),
                                                    opDec.getStateVars(),
                                                    replaceArgs, false);

                                    // Obtain the current location
                                    if (assignParamExp.getLocation() != null) {
                                        // Set the details of the current location
                                        Location ensuresLoc =
                                                (Location) loc.clone();
                                        ensuresLoc
                                                .setDetails("Ensures Clause of "
                                                        + opDec.getName()
                                                        + " from Profile "
                                                        + ope.getName());
                                        Utilities.setLocation(profileEnsures,
                                                ensuresLoc);
                                    }

                                    finalConfirmExp =
                                            myTypeGraph.formConjunct(
                                                    finalConfirmExp,
                                                    profileEnsures);
                                }

                                // Construct the Duration Clause
                                Exp opDur = Exp.copy(ope.getDurationClause());

                                // Replace PostCondition variables in the duration clause
                                opDur =
                                        replaceFormalWithActualEns(opDur, opDec
                                                .getParameters(), opDec
                                                .getStateVars(), replaceArgs,
                                                false);

                                VarExp cumDur =
                                        Utilities
                                                .createVarExp(
                                                        (Location) loc.clone(),
                                                        null,
                                                        Utilities
                                                                .createPosSymbol(Utilities
                                                                        .getCumDur(finalConfirmExp)),
                                                        myTypeGraph.R, null);
                                Exp durCallExp =
                                        Utilities
                                                .createDurCallExp(
                                                        (Location) loc.clone(),
                                                        Integer
                                                                .toString(opDec
                                                                        .getParameters()
                                                                        .size()),
                                                        Z, myTypeGraph.R);
                                InfixExp sumEvalDur =
                                        new InfixExp((Location) loc.clone(),
                                                opDur, Utilities
                                                        .createPosSymbol("+"),
                                                durCallExp);
                                sumEvalDur.setMathType(myTypeGraph.R);
                                sumEvalDur =
                                        new InfixExp((Location) loc.clone(),
                                                Exp.copy(cumDur), Utilities
                                                        .createPosSymbol("+"),
                                                sumEvalDur);
                                sumEvalDur.setMathType(myTypeGraph.R);

                                // For any evaluates mode expression, we need to finalize the variable
                                edu.clemson.cs.r2jt.collections.List<ProgramExp> assignExpList =
                                        assignParamExp.getArguments();
                                for (int i = 0; i < assignExpList.size(); i++) {
                                    ParameterVarDec p =
                                            opDec.getParameters().get(i);
                                    VariableExp pExp =
                                            (VariableExp) assignExpList.get(i);
                                    if (p.getMode() == Mode.EVALUATES) {
                                        VarDec v =
                                                new VarDec(Utilities
                                                        .getVarName(pExp), p
                                                        .getTy());
                                        FunctionExp finalDur =
                                                Utilities.createFinalizAnyDur(
                                                        v, myTypeGraph.R);
                                        sumEvalDur =
                                                new InfixExp(
                                                        (Location) loc.clone(),
                                                        sumEvalDur,
                                                        Utilities
                                                                .createPosSymbol("+"),
                                                        finalDur);
                                        sumEvalDur.setMathType(myTypeGraph.R);
                                    }
                                }

                                // Add duration of assignment and finalize the temporary variable
                                Exp assignDur =
                                        Utilities.createVarExp((Location) loc
                                                .clone(), null, Utilities
                                                .createPosSymbol("Dur_Assgn"),
                                                myTypeGraph.R, null);
                                sumEvalDur =
                                        new InfixExp((Location) loc.clone(),
                                                sumEvalDur, Utilities
                                                        .createPosSymbol("+"),
                                                assignDur);
                                sumEvalDur.setMathType(myTypeGraph.R);

                                Exp finalExpDur =
                                        Utilities.createFinalizAnyDurExp(stmt
                                                .getVar(), myTypeGraph.R,
                                                myCurrentModuleScope);
                                sumEvalDur =
                                        new InfixExp((Location) loc.clone(),
                                                sumEvalDur, Utilities
                                                        .createPosSymbol("+"),
                                                finalExpDur);
                                sumEvalDur.setMathType(myTypeGraph.R);

                                // Replace Cum_Dur in our final ensures clause
                                finalConfirmExp =
                                        Utilities.replace(finalConfirmExp,
                                                cumDur, sumEvalDur);
                                myCurrentAssertiveCode.setFinalConfirm(
                                        finalConfirmExp, finalConfirm
                                                .getSimplify());
                            }
                        }
                        else {
                            Utilities.illegalOperationEnsures(opDec
                                    .getLocation());
                        }
                    }
                    else {
                        Utilities.illegalOperationEnsures(opDec.getLocation());
                    }
                }
                else {
                    Utilities.illegalOperationEnsures(opDec.getLocation());
                }
            }
        }

        // Verbose Mode Debug Messages
        myVCBuffer.append("\nFunction Rule Applied: \n");
        myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
        myVCBuffer.append("\n_____________________ \n");
    }

    /**
     * <p>Applies the if statement rule to the
     * <code>Statement</code>.</p>
     *
     * @param stmt Our current <code>IfStmt</code>.
     */
    private void applyIfStmtRule(IfStmt stmt) {
        // Note: In the If Rule, we will have two instances of the assertive code.
        // One for when the if condition is true and one for the else condition.
        // The current global assertive code variable is going to be used for the if path,
        // and we are going to create a new assertive code for the else path (this includes
        // the case when there is no else clause).
        ProgramExp ifCondition = stmt.getTest();

        // Negation of If (Need to make a copy before we start modifying
        // the current assertive code for the if part)
        AssertiveCode negIfAssertiveCode =
                new AssertiveCode(myCurrentAssertiveCode);

        // Call a method to locate the operation dec for this call
        PosSymbol qualifier = null;
        ProgramParamExp testParamExp = null;

        // Check to see what kind of expression is on the right hand side
        if (ifCondition instanceof ProgramParamExp) {
            // Cast to a ProgramParamExp
            testParamExp = (ProgramParamExp) ifCondition;
        }
        else if (ifCondition instanceof ProgramDotExp) {
            // Cast to a ProgramParamExp
            ProgramDotExp dotExp = (ProgramDotExp) ifCondition;
            testParamExp = (ProgramParamExp) dotExp.getExp();
            qualifier = dotExp.getQualifier();
        }
        else {
            Utilities.expNotHandled(ifCondition, stmt.getLocation());
        }

        Location ifConditionLoc;
        if (ifCondition.getLocation() != null) {
            ifConditionLoc = (Location) ifCondition.getLocation().clone();
        }
        else {
            ifConditionLoc = (Location) stmt.getLocation().clone();
        }

        // Search for the operation dec
        List<PTType> argTypes = new LinkedList<PTType>();
        List<ProgramExp> argsList = testParamExp.getArguments();
        for (ProgramExp arg : argsList) {
            argTypes.add(arg.getProgramType());
        }
        OperationEntry opEntry =
                Utilities.searchOperation(ifCondition.getLocation(), qualifier,
                        testParamExp.getName(), argTypes, myCurrentModuleScope);
        OperationDec opDec = Utilities.convertToOperationDec(opEntry);

        // Check for recursive call of itself
        if (myCurrentOperationEntry != null
                && myOperationDecreasingExp != null
                && myCurrentOperationEntry.getName().equals(opEntry.getName())
                && myCurrentOperationEntry.getReturnType().equals(
                        opEntry.getReturnType())
                && myCurrentOperationEntry.getSourceModuleIdentifier().equals(
                        opEntry.getSourceModuleIdentifier())) {
            // Create a new confirm statement using P_val and the decreasing clause
            VarExp pVal =
                    Utilities.createPValExp(myOperationDecreasingExp
                            .getLocation(), myCurrentModuleScope);

            // Create a new infix expression
            IntegerExp oneExp = new IntegerExp();
            oneExp.setValue(1);
            oneExp.setMathType(myOperationDecreasingExp.getMathType());
            InfixExp leftExp =
                    new InfixExp(stmt.getLocation(), oneExp, Utilities
                            .createPosSymbol("+"), Exp
                            .copy(myOperationDecreasingExp));
            leftExp.setMathType(myOperationDecreasingExp.getMathType());
            InfixExp exp =
                    Utilities.createLessThanEqExp(stmt.getLocation(), leftExp,
                            pVal, BOOLEAN);

            // Create the new confirm statement
            Location loc;
            if (myOperationDecreasingExp.getLocation() != null) {
                loc = (Location) myOperationDecreasingExp.getLocation().clone();
            }
            else {
                loc = (Location) stmt.getLocation().clone();
            }
            loc.setDetails("Show Termination of Recursive Call");
            Utilities.setLocation(exp, loc);
            ConfirmStmt conf = new ConfirmStmt(loc, exp, false);

            // Add it to our list of assertions
            myCurrentAssertiveCode.addCode(conf);
        }

        // Confirm the invoking condition
        // Get the requires clause for this operation
        Exp requires;
        boolean simplify = false;
        if (opDec.getRequires() != null) {
            requires = Exp.copy(opDec.getRequires());

            // Simplify if we just have true
            if (requires.isLiteralTrue()) {
                simplify = true;
            }
        }
        else {
            requires = myTypeGraph.getTrueVarExp();
            simplify = true;
        }

        // Find all the replacements that needs to happen to the requires
        // and ensures clauses
        List<ProgramExp> callArgs = testParamExp.getArguments();
        List<Exp> replaceArgs = modifyArgumentList(callArgs);

        // Replace PreCondition variables in the requires clause
        requires =
                replaceFormalWithActualReq(requires, opDec.getParameters(),
                        replaceArgs);

        // Modify the location of the requires clause and add it to myCurrentAssertiveCode
        // Obtain the current location
        // Note: If we don't have a location, we create one
        Location reqloc;
        if (testParamExp.getName().getLocation() != null) {
            reqloc = (Location) testParamExp.getName().getLocation().clone();
        }
        else {
            reqloc = new Location(null, null);
        }

        // Set the details of the current location
        reqloc.setDetails("Requires Clause of " + opDec.getName());
        Utilities.setLocation(requires, reqloc);

        // Add this to our list of things to confirm
        myCurrentAssertiveCode.addConfirm((Location) reqloc.clone(), requires,
                simplify);

        // Add the if condition as the assume clause
        // Get the ensures clause for this operation
        // Note: If there isn't an ensures clause, it is set to "True"
        Exp ensures, negEnsures = null, opEnsures;
        if (opDec.getEnsures() != null) {
            opEnsures = Exp.copy(opDec.getEnsures());

            // Make sure we have an EqualsExp, else it is an error.
            if (opEnsures instanceof EqualsExp) {
                // Has to be a VarExp on the left hand side (containing the name
                // of the function operation)
                if (((EqualsExp) opEnsures).getLeft() instanceof VarExp) {
                    VarExp leftExp = (VarExp) ((EqualsExp) opEnsures).getLeft();

                    // Check if it has the name of the operation
                    if (leftExp.getName().equals(opDec.getName())) {
                        ensures = ((EqualsExp) opEnsures).getRight();

                        // Obtain the current location
                        Location loc = null;
                        if (testParamExp.getName().getLocation() != null) {
                            // Set the details of the current location
                            loc =
                                    (Location) testParamExp.getName()
                                            .getLocation().clone();
                            loc.setDetails("If Statement Condition");
                            Utilities.setLocation(ensures, loc);
                        }

                        // Replace the formals with the actuals.
                        ensures =
                                replaceFormalWithActualEns(ensures, opDec
                                        .getParameters(), opDec.getStateVars(),
                                        replaceArgs, false);

                        // Replace facility actuals variables in the ensures clause
                        ensures =
                                Utilities.replaceFacilityFormalWithActual(loc,
                                        ensures, opDec.getParameters(),
                                        myInstantiatedFacilityArgMap,
                                        myCurrentModuleScope);

                        myCurrentAssertiveCode.addAssume(loc, ensures, true);

                        // Negation of the condition
                        negEnsures = Utilities.negateExp(ensures, BOOLEAN);
                    }
                    else {
                        Utilities.illegalOperationEnsures(opDec.getLocation());
                    }
                }
                else {
                    Utilities.illegalOperationEnsures(opDec.getLocation());
                }
            }
            else {
                Utilities.illegalOperationEnsures(opDec.getLocation());
            }
        }

        // Create a list for the then clause
        edu.clemson.cs.r2jt.collections.List<Statement> thenStmtList;
        if (stmt.getThenclause() != null) {
            thenStmtList = stmt.getThenclause();
        }
        else {
            thenStmtList =
                    new edu.clemson.cs.r2jt.collections.List<Statement>();
        }

        // Modify the confirm details
        ConfirmStmt ifConfirm = myCurrentAssertiveCode.getFinalConfirm();
        Exp ifConfirmExp = ifConfirm.getAssertion();
        Location ifLocation;
        if (ifConfirmExp.getLocation() != null) {
            ifLocation = (Location) ifConfirmExp.getLocation().clone();
        }
        else {
            ifLocation = (Location) stmt.getLocation().clone();
        }
        String ifDetail =
                ifLocation.getDetails() + ", Condition at "
                        + ifConditionLoc.toString() + " is true";
        ifLocation.setDetails(ifDetail);
        ifConfirmExp.setLocation(ifLocation);

        // NY YS
        // Duration for If Part
        InfixExp sumEvalDur = null;
        if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)) {
            Location loc = (Location) ifLocation.clone();
            VarExp cumDur;
            boolean trueConfirm = false;

            // Our previous rule must have been a while rule
            ConfirmStmt conf = null;
            if (ifConfirmExp.isLiteralTrue() && thenStmtList.size() != 0) {
                Statement st = thenStmtList.get(thenStmtList.size() - 1);
                if (st instanceof ConfirmStmt) {
                    conf = (ConfirmStmt) st;
                    cumDur =
                            Utilities.createVarExp((Location) loc.clone(),
                                    null, Utilities.createPosSymbol(Utilities
                                            .getCumDur(conf.getAssertion())),
                                    myTypeGraph.R, null);
                    trueConfirm = true;
                }
                else {
                    cumDur = null;
                    Utilities.noSuchSymbol(null, "Cum_Dur", loc);
                }
            }
            else {
                cumDur =
                        Utilities.createVarExp((Location) loc.clone(), null,
                                Utilities.createPosSymbol(Utilities
                                        .getCumDur(ifConfirmExp)),
                                myTypeGraph.R, null);
            }

            // Search for operation profile
            OperationProfileEntry ope =
                    Utilities.searchOperationProfile(loc, qualifier,
                            testParamExp.getName(), argTypes,
                            myCurrentModuleScope);
            Exp opDur = Exp.copy(ope.getDurationClause());

            Exp durCallExp =
                    Utilities.createDurCallExp(loc, Integer.toString(opDec
                            .getParameters().size()), Z, myTypeGraph.R);
            sumEvalDur =
                    new InfixExp((Location) loc.clone(), opDur, Utilities
                            .createPosSymbol("+"), durCallExp);
            sumEvalDur.setMathType(myTypeGraph.R);

            Exp sumPlusCumDur =
                    new InfixExp((Location) loc.clone(), Exp.copy(cumDur),
                            Utilities.createPosSymbol("+"), Exp
                                    .copy(sumEvalDur));
            sumPlusCumDur.setMathType(myTypeGraph.R);

            if (trueConfirm && conf != null) {
                // Replace "Cum_Dur" with "Cum_Dur + Dur_Call(<num of args>) + <duration of call>"
                Exp confirm = conf.getAssertion();
                confirm =
                        Utilities.replace(confirm, cumDur, Exp
                                .copy(sumPlusCumDur));
                conf.setAssertion(confirm);
                thenStmtList.set(thenStmtList.size() - 1, conf);
            }
            else {
                // Replace "Cum_Dur" with "Cum_Dur + Dur_Call(<num of args>) + <duration of call>"
                ifConfirmExp =
                        Utilities.replace(ifConfirmExp, cumDur, Exp
                                .copy(sumPlusCumDur));
            }
        }

        // Add the statements inside the if to the assertive code
        myCurrentAssertiveCode.addStatements(thenStmtList);

        // Set the final if confirm
        myCurrentAssertiveCode.setFinalConfirm(ifConfirmExp, ifConfirm
                .getSimplify());

        // Verbose Mode Debug Messages
        myVCBuffer.append("\nIf Part Rule Applied: \n");
        myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
        myVCBuffer.append("\n_____________________ \n");

        // Add the negation of the if condition as the assume clause
        if (negEnsures != null) {
            negIfAssertiveCode.addAssume(ifLocation, negEnsures, true);
        }
        else {
            Utilities.illegalOperationEnsures(opDec.getLocation());
        }

        // Create a list for the then clause
        edu.clemson.cs.r2jt.collections.List<Statement> elseStmtList;
        if (stmt.getElseclause() != null) {
            elseStmtList = stmt.getElseclause();
        }
        else {
            elseStmtList =
                    new edu.clemson.cs.r2jt.collections.List<Statement>();
        }

        // Modify the confirm details
        ConfirmStmt negIfConfirm = negIfAssertiveCode.getFinalConfirm();
        Exp negIfConfirmExp = negIfConfirm.getAssertion();
        Location negIfLocation;
        if (negIfConfirmExp.getLocation() != null) {
            negIfLocation = (Location) negIfConfirmExp.getLocation().clone();
        }
        else {
            negIfLocation = (Location) stmt.getLocation().clone();
        }
        String negIfDetail =
                negIfLocation.getDetails() + ", Condition at "
                        + ifConditionLoc.toString() + " is false";
        negIfLocation.setDetails(negIfDetail);
        negIfConfirmExp.setLocation(negIfLocation);

        // NY YS
        // Duration for Else Part
        if (sumEvalDur != null) {
            Location loc = (Location) negIfLocation.clone();
            VarExp cumDur;
            boolean trueConfirm = false;

            // Our previous rule must have been a while rule
            ConfirmStmt conf = null;
            if (negIfConfirmExp.isLiteralTrue() && elseStmtList.size() != 0) {
                Statement st = elseStmtList.get(elseStmtList.size() - 1);
                if (st instanceof ConfirmStmt) {
                    conf = (ConfirmStmt) st;
                    cumDur =
                            Utilities.createVarExp((Location) loc.clone(),
                                    null, Utilities.createPosSymbol(Utilities
                                            .getCumDur(conf.getAssertion())),
                                    myTypeGraph.R, null);
                    trueConfirm = true;
                }
                else {
                    cumDur = null;
                    Utilities.noSuchSymbol(null, "Cum_Dur", loc);
                }
            }
            else {
                cumDur =
                        Utilities.createVarExp((Location) loc.clone(), null,
                                Utilities.createPosSymbol(Utilities
                                        .getCumDur(negIfConfirmExp)),
                                myTypeGraph.R, null);
            }

            Exp sumPlusCumDur =
                    new InfixExp((Location) loc.clone(), Exp.copy(cumDur),
                            Utilities.createPosSymbol("+"), Exp
                                    .copy(sumEvalDur));
            sumPlusCumDur.setMathType(myTypeGraph.R);

            if (trueConfirm && conf != null) {
                // Replace "Cum_Dur" with "Cum_Dur + Dur_Call(<num of args>) + <duration of call>"
                Exp confirm = conf.getAssertion();
                confirm =
                        Utilities.replace(confirm, cumDur, Exp
                                .copy(sumPlusCumDur));
                conf.setAssertion(confirm);
                elseStmtList.set(elseStmtList.size() - 1, conf);
            }
            else {
                // Replace "Cum_Dur" with "Cum_Dur + Dur_Call(<num of args>) + <duration of call>"
                negIfConfirmExp =
                        Utilities.replace(negIfConfirmExp, cumDur, Exp
                                .copy(sumPlusCumDur));
            }
        }

        // Add the statements inside the else to the assertive code
        negIfAssertiveCode.addStatements(elseStmtList);

        // Set the final else confirm
        negIfAssertiveCode.setFinalConfirm(negIfConfirmExp, negIfConfirm
                .getSimplify());

        // Add this new assertive code to our incomplete assertive code stack
        myIncAssertiveCodeStack.push(negIfAssertiveCode);

        // Verbose Mode Debug Messages
        String newString = "\nNegation of If Part Rule Applied: \n";
        newString += negIfAssertiveCode.assertionToString();
        newString += "\n_____________________ \n";
        myIncAssertiveCodeStackInfo.push(newString);
    }

    /**
     * <p>Applies the initialization rule.</p>
     *
     * @param dec Representation declaration object.
     */
    private void applyInitializationRule(RepresentationDec dec) {
        // Create a new assertive code to hold the correspondence VCs
        AssertiveCode assertiveCode =
                new AssertiveCode(myInstanceEnvironment, dec);

        // Location for the assume clauses
        Location decLoc = dec.getLocation();

        // Add the global constraints as given
        assertiveCode.addAssume((Location) decLoc.clone(),
                myGlobalConstraintExp, false);

        // Add the global require clause as given
        assertiveCode.addAssume((Location) decLoc.clone(), myGlobalRequiresExp,
                false);

        // Search for the type we are implementing
        SymbolTableEntry ste =
                Utilities.searchProgramType(dec.getLocation(), null, dec
                        .getName(), myCurrentModuleScope);

        ProgramTypeEntry typeEntry;
        if (ste instanceof ProgramTypeEntry) {
            typeEntry = ste.toProgramTypeEntry(dec.getLocation());
        }
        else {
            typeEntry =
                    ste.toRepresentationTypeEntry(dec.getLocation())
                            .getDefiningTypeEntry();
        }

        // Make sure we don't have a generic type
        if (typeEntry.getDefiningElement() instanceof TypeDec) {
            // Obtain the original dec from the AST
            TypeDec type = (TypeDec) typeEntry.getDefiningElement();

            // Create a variable expression from the type exemplar
            VarExp exemplar =
                    Utilities.createVarExp(type.getLocation(), null, type
                            .getExemplar(), typeEntry.getModelType(), null);

            // Add any variable declarations for records
            // TODO: Change this! The only variable we need to add is the exemplar
            Exp representationConstraint = myTypeGraph.getTrueVarExp();
            List<ParameterVarDec> fieldAsParameters =
                    new ArrayList<ParameterVarDec>();
            if (dec.getRepresentation() instanceof RecordTy) {
                RecordTy ty = (RecordTy) dec.getRepresentation();
                List<VarDec> decs = ty.getFields();
                assertiveCode.addVariableDecs(decs);

                for (VarDec v : decs) {
                    Ty vTy = v.getTy();

                    // Convert "v" into a parameter for substitution purposes
                    fieldAsParameters.add(new ParameterVarDec(Mode.FIELD, v
                            .getName(), vTy));

                    // Don't do anything if it is a generic type variable
                    if (!(vTy.getProgramTypeValue() instanceof PTGeneric)) {
                        // TODO: We could have a record ty here
                        NameTy vTyAsNameTy = null;
                        if (vTy instanceof NameTy) {
                            vTyAsNameTy = (NameTy) v.getTy();
                        }
                        else {
                            Utilities.tyNotHandled(v.getTy(), v.getLocation());
                        }

                        // Convert the raw type into a variable expression
                        VarExp vTyAsVarExp = null;
                        if (vTyAsNameTy.getQualifier() == null) {
                            for (VarExp varExp : myInstantiatedFacilityArgMap
                                    .keySet()) {
                                if (varExp.getName().getName().equals(
                                        vTyAsNameTy.getName().getName())) {
                                    if (vTyAsVarExp == null) {
                                        vTyAsVarExp = (VarExp) Exp.copy(varExp);
                                    }
                                    else {
                                        Utilities.ambiguousTy(vTy, v
                                                .getLocation());
                                    }
                                }
                            }
                        }
                        else {
                            vTyAsVarExp =
                                    Utilities.createVarExp(vTyAsNameTy
                                            .getLocation(), vTyAsNameTy
                                            .getQualifier(), vTyAsNameTy
                                            .getName(), vTyAsNameTy
                                            .getMathType(), vTyAsNameTy
                                            .getMathTypeValue());
                        }

                        // Create a dotted expression to represent the record field "v"
                        VarExp vAsVarExp =
                                Utilities.createVarExp(v.getLocation(), null, v
                                        .getName(), vTyAsNameTy
                                        .getMathTypeValue(), null);
                        edu.clemson.cs.r2jt.collections.List<Exp> dotExpList =
                                new edu.clemson.cs.r2jt.collections.List<Exp>();
                        dotExpList.add(Exp.copy(exemplar));
                        dotExpList.add(vAsVarExp);
                        DotExp dotExp =
                                Utilities.createDotExp(v.getLocation(),
                                        dotExpList, vTyAsNameTy
                                                .getMathTypeValue());

                        // Obtain the constraint from this field
                        Exp vConstraint =
                                Utilities.retrieveConstraint(v.getLocation(),
                                        vTyAsVarExp, dotExp,
                                        myCurrentModuleScope);
                        if (representationConstraint.isLiteralTrue()) {
                            representationConstraint = vConstraint;
                        }
                        else {
                            representationConstraint =
                                    myTypeGraph.formConjunct(
                                            representationConstraint,
                                            vConstraint);
                        }
                    }
                }
            }

            // Replace facility actuals variables in the representation constraint clause
            representationConstraint =
                    Utilities.replaceFacilityFormalWithActual(decLoc,
                            representationConstraint, fieldAsParameters,
                            myInstantiatedFacilityArgMap, myCurrentModuleScope);

            // Add the representation constraint to our global map
            myRepresentationConstraintMap.put(Utilities.createVarExp(decLoc,
                    null, dec.getName(), dec.getRepresentation()
                            .getMathTypeValue(), null),
                    representationConstraint);

            // Add any statements in the initialization block
            if (dec.getInitialization() != null) {
                InitItem initItem = dec.getInitialization();
                assertiveCode.addStatements(initItem.getStatements());
            }

            // Make sure we have a convention
            Exp conventionExp;
            if (dec.getConvention() == null) {
                conventionExp = myTypeGraph.getTrueVarExp();
            }
            else {
                conventionExp = Exp.copy(dec.getConvention());
            }

            // Set the location for the constraint
            Location loc;
            if (conventionExp.getLocation() != null) {
                loc = (Location) conventionExp.getLocation().clone();
            }
            else {
                loc = (Location) dec.getLocation().clone();
            }
            loc.setDetails("Convention for " + dec.getName().getName());
            Utilities.setLocation(conventionExp, loc);

            // Store the convention in our map
            myRepresentationConventionsMap
                    .put(Utilities.createVarExp(decLoc, null, dec.getName(),
                            dec.getRepresentation().getMathTypeValue(), null),
                            Exp.copy(conventionExp));

            // Add the convention as something we need to confirm
            boolean simplify = false;
            // Simplify if we just have true
            if (conventionExp.isLiteralTrue()) {
                simplify = true;
            }
            Location conventionLoc =
                    (Location) conventionExp.getLocation().clone();
            conventionLoc.setDetails(conventionLoc.getDetails()
                    + " generated by Initialization Rule");
            Utilities.setLocation(conventionExp, conventionLoc);
            assertiveCode.addConfirm(loc, conventionExp, simplify);

            // Add the correspondence as given
            Location corrLoc;
            if (dec.getCorrespondence().getLocation() != null) {
                corrLoc =
                        (Location) dec.getCorrespondence().getLocation()
                                .clone();
            }
            else {
                corrLoc = (Location) decLoc.clone();
            }
            corrLoc.setDetails("Correspondence for " + dec.getName().getName());
            assertiveCode.addAssume(corrLoc, dec.getCorrespondence(), false);

            // Create a variable that refers to the conceptual exemplar
            DotExp conceptualVar =
                    Utilities.createConcVarExp(null, exemplar, typeEntry
                            .getModelType(), BOOLEAN);

            // Make sure we have a constraint
            Exp init;
            if (type.getInitialization().getEnsures() == null) {
                init = myTypeGraph.getTrueVarExp();
            }
            else {
                init = Exp.copy(type.getInitialization().getEnsures());
            }
            init = Utilities.replace(init, exemplar, conceptualVar);

            // Set the location for the constraint
            Location initLoc;
            initLoc = (Location) dec.getLocation().clone();
            initLoc.setDetails("Initialization Rule for "
                    + dec.getName().getName());
            Utilities.setLocation(init, initLoc);

            // Add the initialization as something we need to confirm
            simplify = false;
            // Simplify if we just have true
            if (init.isLiteralTrue()) {
                simplify = true;
            }
            assertiveCode.addConfirm(loc, init, simplify);
        }

        // Add this new assertive code to our incomplete assertive code stack
        myIncAssertiveCodeStack.push(assertiveCode);

        // Verbose Mode Debug Messages
        String newString =
                "\n========================= Type Representation Name:\t"
                        + dec.getName().getName()
                        + " =========================\n";
        newString += "\nInitialization Rule Applied: \n";
        newString += assertiveCode.assertionToString();
        newString += "\n_____________________ \n";
        myIncAssertiveCodeStackInfo.push(newString);
    }

    /**
     * <p>Applies the presume rule to the
     * <code>Statement</code>.</p>
     *
     * @param stmt Our current <code>PresumeStmt</code>.
     */
    private void applyPresumeStmtRule(PresumeStmt stmt) {
        // Convert the presume statement into a confirm and
        // a assume statement.
        ConfirmStmt confirmStmt =
                new ConfirmStmt(stmt.getLocation(), Exp.copy(stmt
                        .getAssertion()), false);
        AssumeStmt assumeStmt =
                new AssumeStmt(stmt.getLocation(), Exp
                        .copy(stmt.getAssertion()), true);

        // Add these statements to our assertive code
        myCurrentAssertiveCode.addCode(confirmStmt);
        myCurrentAssertiveCode.addCode(assumeStmt);

        // Verbose Mode Debug Messages
        myVCBuffer.append("\nPresume Rule Applied: \n");
        myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
        myVCBuffer.append("\n_____________________ \n");
    }

    /**
     * <p>Applies the procedure declaration rule.</p>
     *
     * @param opLoc Location of the procedure declaration.
     * @param name Name of the procedure.
     * @param requires Requires clause
     * @param ensures Ensures clause
     * @param decreasing Decreasing clause (if any)
     * @param procDur Procedure duration clause (if in performance mode)
     * @param varFinalDur Local variable finalization duration clause (if in performance mode)
     * @param parameterVarList List of all parameter variables for this procedure
     * @param variableList List of all variables for this procedure
     * @param statementList List of statements for this procedure
     * @param isLocal True if the it is a local operation. False otherwise.
     */
    private void applyProcedureDeclRule(Location opLoc, String name,
            Exp requires, Exp ensures, Exp decreasing, Exp procDur,
            Exp varFinalDur, List<ParameterVarDec> parameterVarList,
            List<VarDec> variableList, List<Statement> statementList,
            boolean isLocal) {
        // Add the global requires clause
        if (myGlobalRequiresExp != null) {
            myCurrentAssertiveCode.addAssume((Location) opLoc.clone(),
                    myGlobalRequiresExp, false);
        }

        // Add the global constraints
        if (myGlobalConstraintExp != null) {
            myCurrentAssertiveCode.addAssume((Location) opLoc.clone(),
                    myGlobalConstraintExp, false);
        }

        // Only do this if this is not a local operation
        // and we are in a concept realization
        Exp aggConventionExp = null;
        Exp aggCorrespondenceExp = null;
        if (!isLocal) {
            // Do this for all parameters that are type representations
            for (ParameterVarDec parameterVarDec : parameterVarList) {
                NameTy parameterVarDecTy = (NameTy) parameterVarDec.getTy();
                Exp parameterAsVarExp =
                        Utilities.createVarExp(parameterVarDec.getLocation(),
                                null, parameterVarDec.getName(),
                                parameterVarDecTy.getMathTypeValue(), null);

                Set<VarExp> conventionKeys =
                        myRepresentationConventionsMap.keySet();
                for (VarExp varExp : conventionKeys) {
                    // Make sure the qualifiers are the same
                    PosSymbol varExpQual = varExp.getQualifier();
                    PosSymbol parameterTyQual =
                            parameterVarDecTy.getQualifier();

                    if ((varExpQual == null && parameterTyQual == null)
                            || (varExpQual.getName().equals(parameterTyQual
                                    .getName()))) {
                        // Make sure that the type names are the same
                        if (varExp.getName().getName().equals(
                                parameterVarDecTy.getName().getName())) {
                            // Check to see if this is a type representation
                            SymbolTableEntry typeEntry =
                                    Utilities.searchProgramType(opLoc, varExp
                                            .getQualifier(), varExp.getName(),
                                            myCurrentModuleScope);
                            if (typeEntry instanceof RepresentationTypeEntry) {
                                // Replacements
                                MathSymbolEntry exemplarEntry =
                                        typeEntry.toRepresentationTypeEntry(
                                                opLoc).getDefiningTypeEntry()
                                                .getExemplar();
                                Exp exemplar =
                                        Utilities
                                                .createVarExp(
                                                        opLoc,
                                                        null,
                                                        Utilities
                                                                .createPosSymbol(exemplarEntry
                                                                        .getName()),
                                                        exemplarEntry.getType(),
                                                        null);
                                Map<Exp, Exp> replacementMap =
                                        new HashMap<Exp, Exp>();
                                replacementMap.put(exemplar, parameterAsVarExp);

                                // Obtain the convention and substitute formal with actual
                                Exp conventionExp =
                                        Exp.copy(myRepresentationConventionsMap
                                                .get(varExp));
                                conventionExp =
                                        conventionExp
                                                .substitute(replacementMap);

                                // Add the convention as something we need to ensure
                                myCurrentAssertiveCode.addAssume(
                                        (Location) opLoc.clone(),
                                        conventionExp, false);

                                // Store this convention in our aggregated convention exp
                                if (aggConventionExp == null) {
                                    aggConventionExp = Exp.copy(conventionExp);
                                }
                                else {
                                    aggConventionExp =
                                            myTypeGraph.formConjunct(
                                                    aggConventionExp,
                                                    conventionExp);
                                }
                                aggConventionExp.setLocation(conventionExp
                                        .getLocation());
                            }
                        }
                    }
                }

                Set<VarExp> correspondencekeys =
                        myRepresentationCorrespondenceMap.keySet();
                for (VarExp varExp : correspondencekeys) {
                    // Make sure the qualifiers are the same
                    PosSymbol varExpQual = varExp.getQualifier();
                    PosSymbol parameterTyQual =
                            parameterVarDecTy.getQualifier();
                    if ((varExpQual == null && parameterTyQual == null)
                            || (varExpQual.getName().equals(parameterTyQual
                                    .getName()))) {
                        // Make sure that the type names are the same
                        if (varExp.getName().getName().equals(
                                parameterVarDecTy.getName().getName())) {
                            // Check to see if this is a type representation
                            SymbolTableEntry typeEntry =
                                    Utilities.searchProgramType(opLoc, varExp
                                            .getQualifier(), varExp.getName(),
                                            myCurrentModuleScope);
                            if (typeEntry instanceof RepresentationTypeEntry) {
                                // Attempt to replace the correspondence for each parameter
                                Location reqLoc =
                                        (Location) requires.getLocation()
                                                .clone();
                                Exp tmp = Exp.copy(requires);
                                MathSymbolEntry exemplarEntry =
                                        typeEntry.toRepresentationTypeEntry(
                                                opLoc).getDefiningTypeEntry()
                                                .getExemplar();

                                // Replacements
                                Exp exemplar =
                                        Utilities
                                                .createVarExp(
                                                        opLoc,
                                                        null,
                                                        Utilities
                                                                .createPosSymbol(exemplarEntry
                                                                        .getName()),
                                                        exemplarEntry.getType(),
                                                        null);
                                Map<Exp, Exp> replacementMap =
                                        new HashMap<Exp, Exp>();
                                replacementMap.put(exemplar, parameterAsVarExp);

                                // Obtain the correspondence and substitute formal with actual
                                Exp corresponenceExp =
                                        Exp
                                                .copy(myRepresentationCorrespondenceMap
                                                        .get(varExp));
                                corresponenceExp =
                                        corresponenceExp
                                                .substitute(replacementMap);
                                if (corresponenceExp instanceof EqualsExp) {
                                    tmp =
                                            Utilities
                                                    .replace(
                                                            requires,
                                                            ((EqualsExp) corresponenceExp)
                                                                    .getLeft(),
                                                            ((EqualsExp) corresponenceExp)
                                                                    .getRight());
                                }

                                // Well_Def_Corr_Hyp rule: Conjunct the correspondence to
                                // the requires clause. This will ensure that the parsimonious
                                // vc step replaces the requires clause if possible.
                                if (tmp.equals(requires)) {
                                    requires =
                                            myTypeGraph.formConjunct(requires,
                                                    Exp.copy(corresponenceExp));
                                }
                                else {
                                    myCurrentAssertiveCode.addAssume(
                                            (Location) opLoc.clone(), Exp
                                                    .copy(corresponenceExp),
                                            false);
                                    requires = tmp;
                                }
                                requires.setLocation(reqLoc);

                                // Store this correspondence in our aggregated correspondence exp
                                if (aggCorrespondenceExp == null) {
                                    aggCorrespondenceExp =
                                            Exp.copy(corresponenceExp);
                                }
                                else {
                                    aggCorrespondenceExp =
                                            myTypeGraph.formConjunct(
                                                    aggCorrespondenceExp,
                                                    corresponenceExp);
                                }
                            }
                        }
                    }
                }
            }
        }

        myCurrentAssertiveCode.addAssume((Location) opLoc.clone(), requires,
                false);

        // NY - Add any procedure duration clauses
        InfixExp finalDurationExp = null;
        if (procDur != null) {
            // Add Cum_Dur as a free variable
            VarExp cumDur =
                    Utilities.createVarExp((Location) opLoc.clone(), null,
                            Utilities.createPosSymbol("Cum_Dur"),
                            myTypeGraph.R, null);
            myCurrentAssertiveCode.addFreeVar(cumDur);

            // Create 0.0
            VarExp zeroPtZero =
                    Utilities.createVarExp(opLoc, null, Utilities
                            .createPosSymbol("0.0"), myTypeGraph.R, null);

            // Create an equals expression (Cum_Dur = 0.0)
            EqualsExp equalsExp =
                    new EqualsExp(null, Exp.copy(cumDur), EqualsExp.EQUAL,
                            zeroPtZero);
            equalsExp.setMathType(BOOLEAN);
            Location eqLoc = (Location) opLoc.clone();
            eqLoc.setDetails("Initialization of Cum_Dur for Procedure " + name);
            Utilities.setLocation(equalsExp, eqLoc);

            // Add it to our things to assume
            myCurrentAssertiveCode.addAssume((Location) opLoc.clone(),
                    equalsExp, false);

            // Create the duration expression
            Exp durationExp;
            if (varFinalDur != null) {
                durationExp =
                        new InfixExp(null, Exp.copy(cumDur), Utilities
                                .createPosSymbol("+"), varFinalDur);
            }
            else {
                durationExp = Exp.copy(cumDur);
            }
            durationExp.setMathType(myTypeGraph.R);
            Location sumLoc = (Location) opLoc.clone();
            sumLoc
                    .setDetails("Summation of Finalization Duration for Procedure "
                            + name);
            Utilities.setLocation(durationExp, sumLoc);

            finalDurationExp =
                    new InfixExp(null, durationExp, Utilities
                            .createPosSymbol("<="), procDur);
            finalDurationExp.setMathType(BOOLEAN);
            Location andLoc = (Location) opLoc.clone();
            andLoc.setDetails("Duration Clause of " + name);
            Utilities.setLocation(finalDurationExp, andLoc);
        }

        // Add the remember rule
        myCurrentAssertiveCode.addCode(new MemoryStmt((Location) opLoc.clone(),
                true));

        // Add declared variables into the assertion. Also add
        // them to the list of free variables.
        myCurrentAssertiveCode.addVariableDecs(variableList);
        addVarDecsAsFreeVars(variableList);

        // Check to see if we have a recursive procedure.
        // If yes, we will need to create an additional assume clause
        // (P_val = (decreasing clause)) in our list of assertions.
        if (decreasing != null) {
            // Store for future use
            myOperationDecreasingExp = decreasing;

            // Add P_val as a free variable
            VarExp pVal =
                    Utilities.createPValExp(decreasing.getLocation(),
                            myCurrentModuleScope);
            myCurrentAssertiveCode.addFreeVar(pVal);

            // Create an equals expression
            EqualsExp equalsExp =
                    new EqualsExp(null, pVal, EqualsExp.EQUAL, Exp
                            .copy(decreasing));
            equalsExp.setMathType(BOOLEAN);
            Location eqLoc = (Location) decreasing.getLocation().clone();
            eqLoc.setDetails("Progress Metric for Recursive Procedure");
            Utilities.setLocation(equalsExp, eqLoc);

            // Add it to our things to assume
            myCurrentAssertiveCode.addAssume((Location) opLoc.clone(),
                    equalsExp, false);
        }

        // Add the list of statements
        myCurrentAssertiveCode.addStatements(statementList);

        // Add the finalization duration ensures (if any)
        if (finalDurationExp != null) {
            myCurrentAssertiveCode.addConfirm(finalDurationExp.getLocation(),
                    finalDurationExp, false);
        }

        // Correct_Op_Hyp rule: Only applies to non-local operations
        // in concept realizations.
        if (!isLocal && aggConventionExp != null) {
            if (!aggConventionExp.isLiteralTrue()) {
                Location conventionLoc = (Location) opLoc.clone();
                conventionLoc.setDetails(aggConventionExp.getLocation()
                        .getDetails()
                        + " generated by " + name);
                Utilities.setLocation(aggConventionExp, conventionLoc);
                myCurrentAssertiveCode.addConfirm(aggConventionExp
                        .getLocation(), aggConventionExp, false);
            }
        }

        // Well_Def_Corr_Hyp rule: Rather than doing direct replacement,
        // we leave that logic to the parsimonious vc step. A replacement
        // will occur if this is a correspondence function or an implies
        // will be formed if this is a correspondence relation.
        if (!isLocal && aggCorrespondenceExp != null) {
            myCurrentAssertiveCode.addAssume((Location) opLoc.clone(),
                    aggCorrespondenceExp, false);
        }

        // Add the final confirms clause
        myCurrentAssertiveCode.setFinalConfirm(ensures, false);

        // Verbose Mode Debug Messages
        myVCBuffer.append("\nProcedure Declaration Rule Applied: \n");
        myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
        myVCBuffer.append("\n_____________________ \n");
    }

    /**
     * <p>Applies the remember rule.</p>
     */
    private void applyRememberRule() {
        // Obtain the final confirm and apply the remember method for Exp
        ConfirmStmt confirmStmt = myCurrentAssertiveCode.getFinalConfirm();
        Exp conf = confirmStmt.getAssertion();
        conf = conf.remember();
        myCurrentAssertiveCode.setFinalConfirm(conf, confirmStmt.getSimplify());

        // Verbose Mode Debug Messages
        myVCBuffer.append("\nRemember Rule Applied: \n");
        myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
        myVCBuffer.append("\n_____________________ \n");
    }

    /**
     * <p>Applies each of the proof rules. This <code>AssertiveCode</code> will be
     * stored for later use and therefore should be considered immutable after
     * a call to this method.</p>
     */
    private void applyRules() {
        // Apply a proof rule to each of the assertions
        while (myCurrentAssertiveCode.hasAnotherAssertion()) {
            // Work our way from the last assertion
            VerificationStatement curAssertion =
                    myCurrentAssertiveCode.getLastAssertion();

            switch (curAssertion.getType()) {
            // Change Assertion
            case VerificationStatement.CHANGE:
                applyChangeRule(curAssertion);
                break;
            // Code
            case VerificationStatement.CODE:
                applyCodeRules((Statement) curAssertion.getAssertion());
                break;
            // Variable Declaration Assertion
            case VerificationStatement.VARIABLE:
                applyVarDeclRule(curAssertion);
                break;
            }
        }
    }

    /**
     * <p>Applies the swap statement rule to the
     * <code>Statement</code>.</p>
     *
     * @param stmt Our current <code>SwapStmt</code>.
     */
    private void applySwapStmtRule(SwapStmt stmt) {
        // Obtain the current final confirm clause
        ConfirmStmt confirmStmt = myCurrentAssertiveCode.getFinalConfirm();
        Exp conf = confirmStmt.getAssertion();

        // Create a copy of the left and right hand side
        VariableExp stmtLeft = (VariableExp) Exp.copy(stmt.getLeft());
        VariableExp stmtRight = (VariableExp) Exp.copy(stmt.getRight());

        // New left and right
        Exp newLeft = Utilities.convertExp(stmtLeft, myCurrentModuleScope);
        Exp newRight = Utilities.convertExp(stmtRight, myCurrentModuleScope);

        // Use our final confirm to obtain the math types
        List lst = conf.getSubExpressions();
        for (int i = 0; i < lst.size(); i++) {
            if (lst.get(i) instanceof VarExp) {
                VarExp thisExp = (VarExp) lst.get(i);
                if (newRight instanceof VarExp) {
                    if (thisExp.getName().equals(
                            ((VarExp) newRight).getName().getName())) {
                        newRight.setMathType(thisExp.getMathType());
                        newRight.setMathTypeValue(thisExp.getMathTypeValue());
                    }
                }
                if (newLeft instanceof VarExp) {
                    if (thisExp.getName().equals(
                            ((VarExp) newLeft).getName().getName())) {
                        newLeft.setMathType(thisExp.getMathType());
                        newLeft.setMathTypeValue(thisExp.getMathTypeValue());
                    }
                }
            }
        }

        // Temp variable
        VarExp tmp = new VarExp();
        tmp.setName(Utilities.createPosSymbol("_"
                + Utilities.getVarName(stmtLeft).getName()));
        tmp.setMathType(stmtLeft.getMathType());
        tmp.setMathTypeValue(stmtLeft.getMathTypeValue());

        // Replace according to the swap rule
        conf = Utilities.replace(conf, newRight, tmp);
        conf = Utilities.replace(conf, newLeft, newRight);
        conf = Utilities.replace(conf, tmp, newLeft);

        // NY YS
        // Duration for swap statements
        if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)) {
            Location loc = stmt.getLocation();
            VarExp cumDur =
                    Utilities
                            .createVarExp((Location) loc.clone(), null,
                                    Utilities.createPosSymbol(Utilities
                                            .getCumDur(conf)), myTypeGraph.R,
                                    null);

            Exp swapDur =
                    Utilities.createVarExp((Location) loc.clone(), null,
                            Utilities.createPosSymbol("Dur_Swap"),
                            myTypeGraph.R, null);
            InfixExp sumSwapDur =
                    new InfixExp((Location) loc.clone(), Exp.copy(cumDur),
                            Utilities.createPosSymbol("+"), swapDur);
            sumSwapDur.setMathType(myTypeGraph.R);

            conf = Utilities.replace(conf, cumDur, sumSwapDur);
        }

        // Set this new expression as the new final confirm
        myCurrentAssertiveCode.setFinalConfirm(conf, confirmStmt.getSimplify());

        // Verbose Mode Debug Messages
        myVCBuffer.append("\nSwap Rule Applied: \n");
        myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
        myVCBuffer.append("\n_____________________ \n");
    }

    /**
     * <p>Applies the variable declaration rule.</p>
     *
     * @param var A declared variable stored as a
     *            <code>VerificationStatement</code>
     */
    private void applyVarDeclRule(VerificationStatement var) {
        // Obtain the variable from the verification statement
        VarDec varDec = (VarDec) var.getAssertion();
        ProgramTypeEntry typeEntry;

        // Ty is NameTy
        if (varDec.getTy() instanceof NameTy) {
            NameTy pNameTy = (NameTy) varDec.getTy();

            // Query for the type entry in the symbol table
            SymbolTableEntry ste =
                    Utilities.searchProgramType(pNameTy.getLocation(), pNameTy
                            .getQualifier(), pNameTy.getName(),
                            myCurrentModuleScope);

            if (ste instanceof ProgramTypeEntry) {
                typeEntry = ste.toProgramTypeEntry(pNameTy.getLocation());
            }
            else {
                typeEntry =
                        ste.toRepresentationTypeEntry(pNameTy.getLocation())
                                .getDefiningTypeEntry();
            }

            // Make sure we don't have a generic type
            if (typeEntry.getDefiningElement() instanceof TypeDec) {
                // Obtain the original dec from the AST
                TypeDec type = (TypeDec) typeEntry.getDefiningElement();

                // Create a variable expression from the declared variable
                VarExp varDecExp =
                        Utilities.createVarExp(varDec.getLocation(), null,
                                varDec.getName(), typeEntry.getModelType(),
                                null);

                // Create a variable expression from the type exemplar
                VarExp exemplar =
                        Utilities.createVarExp(type.getLocation(), null, type
                                .getExemplar(), typeEntry.getModelType(), null);

                // Deep copy the original initialization ensures
                Exp init = Exp.copy(type.getInitialization().getEnsures());
                init = Utilities.replace(init, exemplar, varDecExp);

                // Set the location for the initialization ensures
                Location loc;
                if (init.getLocation() != null) {
                    loc = (Location) init.getLocation().clone();
                }
                else {
                    loc = (Location) type.getLocation().clone();
                }
                loc.setDetails("Initialization ensures on "
                        + varDec.getName().getName());
                Utilities.setLocation(init, loc);

                // Final confirm clause
                Exp finalConfirm =
                        myCurrentAssertiveCode.getFinalConfirm().getAssertion();

                // Obtain the string form of the variable
                String varName = varDec.getName().getName();

                // Check to see if we have a variable dot expression.
                // If we do, we will need to extract the name.
                int dotIndex = varName.indexOf(".");
                if (dotIndex > 0) {
                    varName = varName.substring(0, dotIndex);
                }

                // Check to see if this variable was declared inside a record
                ResolveConceptualElement element =
                        myCurrentAssertiveCode.getInstantiatingElement();
                if (element instanceof RepresentationDec) {
                    RepresentationDec dec = (RepresentationDec) element;

                    if (dec.getRepresentation() instanceof RecordTy) {
                        SymbolTableEntry repSte =
                                Utilities.searchProgramType(dec.getLocation(),
                                        null, dec.getName(),
                                        myCurrentModuleScope);

                        ProgramTypeDefinitionEntry representationTypeEntry =
                                repSte.toRepresentationTypeEntry(
                                        pNameTy.getLocation())
                                        .getDefiningTypeEntry();

                        // Create a variable expression from the type exemplar
                        VarExp representationExemplar =
                                Utilities
                                        .createVarExp(
                                                varDec.getLocation(),
                                                null,
                                                Utilities
                                                        .createPosSymbol(representationTypeEntry
                                                                .getExemplar()
                                                                .getName()),
                                                representationTypeEntry
                                                        .getModelType(), null);

                        // Create a dotted expression
                        edu.clemson.cs.r2jt.collections.List<Exp> expList =
                                new edu.clemson.cs.r2jt.collections.List<Exp>();
                        expList.add(representationExemplar);
                        expList.add(varDecExp);
                        DotExp dotExp =
                                Utilities.createDotExp(loc, expList, varDecExp
                                        .getMathType());

                        // Replace the initialization clauses appropriately
                        init = Utilities.replace(init, varDecExp, dotExp);
                    }
                }

                // Replace facility actuals variables in the init clause
                List<ParameterVarDec> varDecAsParameter =
                        new ArrayList<ParameterVarDec>();
                varDecAsParameter.add(new ParameterVarDec(Mode.LOCAL, varDec
                        .getName(), varDec.getTy()));
                init =
                        Utilities.replaceFacilityFormalWithActual(
                                (Location) loc.clone(), init,
                                varDecAsParameter,
                                myInstantiatedFacilityArgMap,
                                myCurrentModuleScope);

                // Check if our confirm clause uses this variable
                if (finalConfirm.containsVar(varName, false)) {
                    // Add the new assume clause to our assertive code.
                    myCurrentAssertiveCode.addAssume((Location) loc.clone(),
                            init, false);
                }
            }
            // Since the type is generic, we can only use the is_initial predicate
            // to ensure that the value is initial value.
            else {
                // Obtain the original dec from the AST
                Location varLoc = varDec.getLocation();

                // Create an is_initial dot expression
                DotExp isInitialExp =
                        Utilities.createInitExp(varDec, MTYPE, BOOLEAN);
                if (varLoc != null) {
                    Location loc = (Location) varLoc.clone();
                    loc.setDetails("Initial Value for "
                            + varDec.getName().getName());
                    Utilities.setLocation(isInitialExp, loc);
                }

                // Add to our assertive code as an assume
                myCurrentAssertiveCode.addAssume(varLoc, isInitialExp, false);
            }

            // NY YS
            // Initialization duration for this variable
            if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)) {
                ConfirmStmt finalConfirmStmt =
                        myCurrentAssertiveCode.getFinalConfirm();
                Exp finalConfirm = finalConfirmStmt.getAssertion();

                Location loc =
                        ((NameTy) varDec.getTy()).getName().getLocation();
                VarExp cumDur =
                        Utilities.createVarExp((Location) loc.clone(), null,
                                Utilities.createPosSymbol(Utilities
                                        .getCumDur(finalConfirm)),
                                myTypeGraph.R, null);
                Exp initDur = Utilities.createInitAnyDur(varDec, myTypeGraph.R);
                InfixExp sumInitDur =
                        new InfixExp((Location) loc.clone(), Exp.copy(cumDur),
                                Utilities.createPosSymbol("+"), initDur);
                sumInitDur.setMathType(myTypeGraph.R);

                finalConfirm =
                        Utilities.replace(finalConfirm, cumDur, sumInitDur);
                myCurrentAssertiveCode.setFinalConfirm(finalConfirm,
                        finalConfirmStmt.getSimplify());
            }

            // Verbose Mode Debug Messages
            myVCBuffer.append("\nVariable Declaration Rule Applied: \n");
            myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
            myVCBuffer.append("\n_____________________ \n");
        }
        else {
            // Ty not handled.
            Utilities.tyNotHandled(varDec.getTy(), varDec.getLocation());
        }
    }

    /**
     * <p>Applies the while statement rule.</p>
     *
     * @param stmt Our current <code>WhileStmt</code>.
     */
    private void applyWhileStmtRule(WhileStmt stmt) {
        // Obtain the loop invariant
        Exp invariant;
        boolean simplifyInvariant = false;
        if (stmt.getMaintaining() != null) {
            invariant = Exp.copy(stmt.getMaintaining());
            invariant.setMathType(stmt.getMaintaining().getMathType());

            // Simplify if we just have true
            if (invariant.isLiteralTrue()) {
                simplifyInvariant = true;
            }
        }
        else {
            invariant = myTypeGraph.getTrueVarExp();
            simplifyInvariant = true;
        }

        // NY YS
        // Obtain the elapsed time duration of loop
        Exp elapsedTimeDur = null;
        if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)) {
            if (stmt.getElapsed_Time() != null) {
                elapsedTimeDur = Exp.copy(stmt.getElapsed_Time());
                elapsedTimeDur.setMathType(myTypeGraph.R);
            }
        }

        // Confirm the base case of invariant
        Exp baseCase = Exp.copy(invariant);
        Location baseLoc;
        if (invariant.getLocation() != null) {
            baseLoc = (Location) invariant.getLocation().clone();
        }
        else {
            baseLoc = (Location) stmt.getLocation().clone();
        }
        baseLoc.setDetails("Base Case of the Invariant of While Statement");
        Utilities.setLocation(baseCase, baseLoc);

        // NY YS
        // Confirm that elapsed time is 0.0
        if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)
                && elapsedTimeDur != null) {
            Exp initElapseDurExp = Exp.copy(elapsedTimeDur);
            Location initElapseLoc;
            if (elapsedTimeDur != null && elapsedTimeDur.getLocation() != null) {
                initElapseLoc = (Location) elapsedTimeDur.getLocation().clone();
            }
            else {
                initElapseLoc = (Location) elapsedTimeDur.getLocation().clone();
            }
            initElapseLoc
                    .setDetails("Base Case of Elapsed Time Duration of While Statement");
            Utilities.setLocation(initElapseDurExp, initElapseLoc);
            Exp zeroEqualExp =
                    new EqualsExp((Location) initElapseLoc.clone(),
                            initElapseDurExp, 1, Utilities.createVarExp(
                                    (Location) initElapseLoc.clone(), null,
                                    Utilities.createPosSymbol("0.0"),
                                    myTypeGraph.R, null));
            zeroEqualExp.setMathType(BOOLEAN);
            baseCase = myTypeGraph.formConjunct(baseCase, zeroEqualExp);
        }
        myCurrentAssertiveCode.addConfirm((Location) baseLoc.clone(), baseCase,
                simplifyInvariant);

        // Add the change rule
        if (stmt.getChanging() != null) {
            myCurrentAssertiveCode.addChange(stmt.getChanging());
        }

        // Assume the invariant and NQV(RP, P_Val) = P_Exp
        Location whileLoc = stmt.getLocation();
        Exp assume;
        Exp finalConfirm =
                myCurrentAssertiveCode.getFinalConfirm().getAssertion();
        boolean simplifyFinalConfirm =
                myCurrentAssertiveCode.getFinalConfirm().getSimplify();
        Exp decreasingExp = stmt.getDecreasing();
        Exp nqv;

        if (decreasingExp != null) {
            VarExp pval =
                    Utilities.createPValExp((Location) whileLoc.clone(),
                            myCurrentModuleScope);
            nqv = Utilities.createQuestionMarkVariable(finalConfirm, pval);
            nqv.setMathType(pval.getMathType());
            Exp equalPExp =
                    new EqualsExp((Location) whileLoc.clone(), Exp.copy(nqv),
                            1, Exp.copy(decreasingExp));
            equalPExp.setMathType(BOOLEAN);
            assume = myTypeGraph.formConjunct(Exp.copy(invariant), equalPExp);
        }
        else {
            decreasingExp = myTypeGraph.getTrueVarExp();
            nqv = myTypeGraph.getTrueVarExp();
            assume = Exp.copy(invariant);
        }

        // NY YS
        // Also assume NQV(RP, Cum_Dur) = El_Dur_Exp
        Exp nqv2 = null;
        if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)
                & elapsedTimeDur != null) {
            VarExp cumDurExp =
                    Utilities.createVarExp((Location) whileLoc.clone(), null,
                            Utilities.createPosSymbol("Cum_Dur"),
                            myTypeGraph.R, null);
            nqv2 =
                    Utilities.createQuestionMarkVariable(finalConfirm,
                            cumDurExp);
            nqv2.setMathType(cumDurExp.getMathType());
            Exp equalPExp =
                    new EqualsExp((Location) whileLoc.clone(), Exp.copy(nqv2),
                            1, Exp.copy(elapsedTimeDur));
            equalPExp.setMathType(BOOLEAN);
            assume = myTypeGraph.formConjunct(assume, equalPExp);
        }

        myCurrentAssertiveCode.addAssume((Location) whileLoc.clone(), assume,
                false);

        // if statement body (need to deep copy!)
        edu.clemson.cs.r2jt.collections.List<Statement> ifStmtList =
                new edu.clemson.cs.r2jt.collections.List<Statement>();
        edu.clemson.cs.r2jt.collections.List<Statement> whileStmtList =
                stmt.getStatements();
        for (Statement s : whileStmtList) {
            ifStmtList.add((Statement) s.clone());
        }

        // Confirm the inductive case of invariant
        Exp inductiveCase = Exp.copy(invariant);
        Location inductiveLoc;
        if (invariant.getLocation() != null) {
            inductiveLoc = (Location) invariant.getLocation().clone();
        }
        else {
            inductiveLoc = (Location) stmt.getLocation().clone();
        }
        inductiveLoc
                .setDetails("Inductive Case of Invariant of While Statement");
        Utilities.setLocation(inductiveCase, inductiveLoc);
        ifStmtList.add(new ConfirmStmt(inductiveLoc, inductiveCase,
                simplifyInvariant));

        // Confirm the termination of the loop.
        if (decreasingExp != null) {
            Location decreasingLoc =
                    (Location) decreasingExp.getLocation().clone();
            if (decreasingLoc != null) {
                decreasingLoc.setDetails("Termination of While Statement");
            }

            // Create a new infix expression
            IntegerExp oneExp = new IntegerExp();
            oneExp.setValue(1);
            oneExp.setMathType(decreasingExp.getMathType());
            InfixExp leftExp =
                    new InfixExp(stmt.getLocation(), oneExp, Utilities
                            .createPosSymbol("+"), Exp.copy(decreasingExp));
            leftExp.setMathType(decreasingExp.getMathType());
            Exp infixExp =
                    Utilities.createLessThanEqExp(decreasingLoc, leftExp, Exp
                            .copy(nqv), BOOLEAN);

            // Confirm NQV(RP, Cum_Dur) <= El_Dur_Exp
            if (nqv2 != null) {
                Location elapsedTimeLoc =
                        (Location) elapsedTimeDur.getLocation().clone();
                if (elapsedTimeLoc != null) {
                    elapsedTimeLoc.setDetails("Termination of While Statement");
                }

                Exp infixExp2 =
                        Utilities.createLessThanEqExp(elapsedTimeLoc, Exp
                                .copy(nqv2), Exp.copy(elapsedTimeDur), BOOLEAN);

                infixExp = myTypeGraph.formConjunct(infixExp, infixExp2);
                infixExp.setLocation(decreasingLoc);
            }

            ifStmtList.add(new ConfirmStmt(decreasingLoc, infixExp, false));
        }
        else {
            throw new RuntimeException("No decreasing clause!");
        }

        // empty elseif pair
        edu.clemson.cs.r2jt.collections.List<ConditionItem> elseIfPairList =
                new edu.clemson.cs.r2jt.collections.List<ConditionItem>();

        // else body
        Location elseConfirmLoc;
        if (finalConfirm.getLocation() != null) {
            elseConfirmLoc = (Location) finalConfirm.getLocation().clone();
        }
        else {
            elseConfirmLoc = (Location) whileLoc.clone();
        }
        edu.clemson.cs.r2jt.collections.List<Statement> elseStmtList =
                new edu.clemson.cs.r2jt.collections.List<Statement>();

        // NY YS
        // Form the confirm clause for the else
        Exp elseConfirm = Exp.copy(finalConfirm);
        if (myInstanceEnvironment.flags.isFlagSet(FLAG_ALTPVCS_VC)
                & elapsedTimeDur != null) {
            Location loc = stmt.getLocation();
            VarExp cumDur =
                    Utilities.createVarExp((Location) loc.clone(), null,
                            Utilities.createPosSymbol(Utilities
                                    .getCumDur(elseConfirm)), myTypeGraph.R,
                            null);
            InfixExp sumWhileDur =
                    new InfixExp((Location) loc.clone(), Exp.copy(cumDur),
                            Utilities.createPosSymbol("+"), Exp
                                    .copy(elapsedTimeDur));
            sumWhileDur.setMathType(myTypeGraph.R);

            elseConfirm = Utilities.replace(elseConfirm, cumDur, sumWhileDur);
        }

        elseStmtList.add(new ConfirmStmt(elseConfirmLoc, elseConfirm,
                simplifyFinalConfirm));

        // condition
        ProgramExp condition = (ProgramExp) Exp.copy(stmt.getTest());
        if (condition.getLocation() != null) {
            Location condLoc = (Location) condition.getLocation().clone();
            condLoc.setDetails("While Loop Condition");
            Utilities.setLocation(condition, condLoc);
        }

        // add it back to your assertive code
        IfStmt newIfStmt =
                new IfStmt(condition, ifStmtList, elseIfPairList, elseStmtList);
        myCurrentAssertiveCode.addCode(newIfStmt);

        // Change our final confirm to "True"
        Exp trueVarExp = myTypeGraph.getTrueVarExp();
        trueVarExp.setLocation((Location) whileLoc.clone());
        myCurrentAssertiveCode.setFinalConfirm(trueVarExp, true);

        // Verbose Mode Debug Messages
        myVCBuffer.append("\nWhile Rule Applied: \n");
        myVCBuffer.append(myCurrentAssertiveCode.assertionToString());
        myVCBuffer.append("\n_____________________ \n");
    }

}