/**
 * CongruenceClassProver.java
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
package edu.clemson.cs.r2jt.congruenceclassprover;

import edu.clemson.cs.r2jt.data.ModuleID;
import edu.clemson.cs.r2jt.init.CompileEnvironment;
import edu.clemson.cs.r2jt.misc.Flag;
import edu.clemson.cs.r2jt.misc.FlagDependencies;
import edu.clemson.cs.r2jt.misc.FlagManager;
import edu.clemson.cs.r2jt.rewriteprover.Metrics;
import edu.clemson.cs.r2jt.rewriteprover.Prover;
import edu.clemson.cs.r2jt.rewriteprover.ProverListener;
import edu.clemson.cs.r2jt.rewriteprover.VC;
import edu.clemson.cs.r2jt.rewriteprover.absyn.PExp;
import edu.clemson.cs.r2jt.rewriteprover.absyn.PSymbol;
import edu.clemson.cs.r2jt.rewriteprover.model.PerVCProverModel;
import edu.clemson.cs.r2jt.typeandpopulate.MTType;
import edu.clemson.cs.r2jt.typeandpopulate.MathSymbolTable;
import edu.clemson.cs.r2jt.typeandpopulate.ModuleScope;
import edu.clemson.cs.r2jt.typeandpopulate.SymbolNotOfKindTypeException;
import edu.clemson.cs.r2jt.typeandpopulate.entry.MathSymbolEntry;
import edu.clemson.cs.r2jt.typeandpopulate.entry.TheoremEntry;
import edu.clemson.cs.r2jt.typeandpopulate.query.EntryTypeQuery;
import edu.clemson.cs.r2jt.typeandpopulate.query.NameQuery;
import edu.clemson.cs.r2jt.typereasoning.TypeGraph;
import edu.clemson.cs.r2jt.vcgeneration.VCGenerator;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.concurrent.TimeUnit;

/**
 * Created by mike on 4/4/2014.
 */
public final class CongruenceClassProver {

    public static final Flag FLAG_PROVE =
            new Flag(Prover.FLAG_SECTION_NAME, "ccprove",
                    "congruence closure based prover");
    private static final String[] NUMTRIES_ARGS = { "numtries" };
    public static final Flag FLAG_NUMTRIES =
            new Flag("Proving", "num_tries",
                    "Prover will halt after this many timeouts.",
                    NUMTRIES_ARGS, Flag.Type.HIDDEN);
    private final List<ClauseSet> m_ccVCs;
    private final CompileEnvironment m_environment;
    private final ModuleScope m_scope;
    private final long DEFAULTTIMEOUT = 50000;
    private final boolean SHOWRESULTSIFNOTPROVED = true;
    private final TypeGraph m_typeGraph;
    // only for webide ////////////////////////////////////
    private final PerVCProverModel[] myModels;
    private final int numUsesBeforeQuit; // weird bug if this isn't final
    private final int DEFAULTTRIES = -1; // -1 to not skip
    private String m_results;
    private boolean printVCEachStep = false;
    private ProverListener myProverListener;
    private long myTimeout;
    private long totalTime = 0;

    public CongruenceClassProver(TypeGraph g, List<VC> vcs, ModuleScope scope,
                                 CompileEnvironment environment, ProverListener listener) {

        // Only for web ide //////////////////////////////////////////
        myModels = new PerVCProverModel[vcs.size()];
        if (listener != null) {
            myProverListener = listener;
        }
        if (environment.flags.isFlagSet(Prover.FLAG_TIMEOUT)) {
            myTimeout =
                    Integer.parseInt(environment.flags.getFlagArgument(
                            Prover.FLAG_TIMEOUT, Prover.FLAG_TIMEOUT_ARG_NAME));
        } else {
            myTimeout = DEFAULTTIMEOUT;
        }
        if (environment.flags.isFlagSet(CongruenceClassProver.FLAG_NUMTRIES)) {
            numUsesBeforeQuit =
                    Integer.parseInt(environment.flags.getFlagArgument(
                            CongruenceClassProver.FLAG_NUMTRIES, "numtries"));
        } else {
            numUsesBeforeQuit = DEFAULTTRIES;
        }

        ///////////////////////////////////////////////////////////////
        totalTime = System.currentTimeMillis();
        m_typeGraph = g;
        m_ccVCs = new ArrayList<>();
        int i = 0;

        List<TheoremEntry> theoremEntries =
                scope.query(new EntryTypeQuery(TheoremEntry.class,
                        MathSymbolTable.ImportStrategy.IMPORT_RECURSIVE,
                        MathSymbolTable.FacilityStrategy.FACILITY_IGNORE));
        List<edu.clemson.cs.r2jt.typeandpopulate.entry.SymbolTableEntry> z_entries =
                scope.query(new NameQuery(null, "Z",
                        MathSymbolTable.ImportStrategy.IMPORT_RECURSIVE,
                        MathSymbolTable.FacilityStrategy.FACILITY_INSTANTIATE,
                        false));
        MTType z = null;
        if (z_entries != null && z_entries.size() > 0) {
            MathSymbolEntry z_e = (MathSymbolEntry) z_entries.get(0);
            try {
                z = z_e.getTypeValue();
            } catch (SymbolNotOfKindTypeException e) {
                e.printStackTrace();
            }
        }

        List<edu.clemson.cs.r2jt.typeandpopulate.entry.SymbolTableEntry> n_entries =
                scope.query(new NameQuery(null, "N",
                        //MathSymbolTable.ImportStrategy.IMPORT_RECURSIVE,
                        MathSymbolTable.ImportStrategy.IMPORT_NAMED,
                        MathSymbolTable.FacilityStrategy.FACILITY_INSTANTIATE,
                        false));
        MTType n = null;
        if (n_entries != null && n_entries.size() > 0) {
            MathSymbolEntry n_e = (MathSymbolEntry) n_entries.get(0);
            try {
                n = n_e.getTypeValue();
            } catch (SymbolNotOfKindTypeException e) {
                e.printStackTrace();
            }
        }
        //printVCEachStep = true;
        if(false) {
            String[] exA = new String[]{"x.f.f.fx.=", "x.f.f.f.f.fx.=", "a.fa.=.~"};
            // p(x,y) implies q(x,y) or x = y  p is <=, q is <
            // p(a,b)
            // not(a=b)
            // not q(a,b)
            String[] exB = new String[]{"xy.pxy.qxy.=.|.>", "ab.p", "ab.=.~", "ab.q.~"};
            // f(e) = e :: f is Reverse, e is empty String
            // g(e,x) = x :: g is concat, x is any string
            // t = e;
            // prove: G(f(t),a) = a
            String[] exC = new String[]{"e.fe.=", "ex.Gx.=", "te.=", "t.fa.Ga.=.~"};
            /*
            C1. p(g(x,y)) or q(y)
            C2. g(x,y) = h(x).
            C3. not p(g(a,b))
            C4. not(q(b))
             */
            String[][] examples = {exA, exB, exC};
            for (String[] ex : examples) {
                ClauseSet temp = new ClauseSet(m_typeGraph, z, n, "");
                for (String e : ex) {
                    PExp p = Utilities.stringToPExp(e, g);
                    temp.addClause(p);
                }
                temp.initializeTermStore();
                int isproved = temp.prove(50);
                System.out.println(temp.log + isproved);
            }
        }
        PExp sumC = sumConversion(n,z);
        for (VC vc : vcs) {
            //if(!vc.getName().equals("0_4")) continue;
            // make every PExp a PSymbol
            vc.convertAllToPsymbols(m_typeGraph);

            ClauseSet vccs = new ClauseSet(m_typeGraph,z,n, vc.getName());
            vccs.addVC(vc);
            //vccs.addClause(sumC);
            m_ccVCs.add(vccs);
            myModels[i++] = (new PerVCProverModel(g, vc.getName(), vc, null));

        }

        for (TheoremEntry e : theoremEntries) {
            String smdi = e.getSourceModuleIdentifier().toString();
            if (!(  smdi.contains("String_Theory") ||smdi.contains("Natural_Number_Theory"))) {
                continue;
            }

            for(ClauseSet cs: m_ccVCs){
                cs.addClause(e.getAssertion());
            }

        }


        m_environment = environment;
        m_scope = scope;
        m_results = "";

    }

    // Temporarily coding conversion theorem for natural / integer addition
    // forall x,y:N, +N(x,y) = +Z(x,y) match left only
    PSymbol sumConversion(MTType n, MTType z) {
        PSymbol x = new PSymbol(n, null, "x", PSymbol.Quantification.FOR_ALL);
        PSymbol y = new PSymbol(n, null, "y", PSymbol.Quantification.FOR_ALL);
        ArrayList<PExp> args = new ArrayList<PExp>();
        args.add(x);
        args.add(y);
        PSymbol nPlus = new PSymbol(n, null, "+:N", args);
        PSymbol zPlus = new PSymbol(z, null, "+:Z", args);
        args.clear();
        args.add(nPlus);
        args.add(zPlus);
        PSymbol eq = new PSymbol(m_typeGraph.BOOLEAN, null, "=", args);
        return eq;
    }

    ///////////////////////////////////////////////////////
    public static void setUpFlags() {
        /*FlagDependencies.addExcludes(FLAG_PROVE, Prover.FLAG_PROVE);
        FlagDependencies.addExcludes(FLAG_PROVE, Prover.FLAG_LEGACY_PROVE);
        FlagDependencies.addImplies(FLAG_PROVE, Prover.FLAG_SOME_PROVER);
         */

        // for new vc gen
        FlagDependencies.addImplies(CongruenceClassProver.FLAG_PROVE,
                VCGenerator.FLAG_ALTVERIFY_VC);
        FlagDependencies.addRequires(CongruenceClassProver.FLAG_NUMTRIES,
                CongruenceClassProver.FLAG_PROVE);
    }

    public void start() throws IOException {

        String summary = "";
        int i = 0;
        int numUnproved = 0;
        Iterator<ClauseSet> csIt = m_ccVCs.iterator();
        while (csIt.hasNext()) {
            ClauseSet vcc = csIt.next();
            //if(!vcc.tag.equals("0_3")) continue;
            long startTime = System.nanoTime();
            //printVCEachStep = true;
            //if (!vcc.m_name.equals("0_2")) continue;
            String whyQuit = "";
            // Skip proof loop
            if (numUsesBeforeQuit >= 0 && numUnproved >= numUsesBeforeQuit) {
                if (myProverListener != null) {
                    myProverListener.vcResult(false, myModels[i], new Metrics(
                            0, 0));
                }
                summary += vcc.tag + " skipped\n";
                ++i;
                continue;
            }
            vcc.initializeTermStore();
            int proved = vcc.prove(DEFAULTTIMEOUT);
            m_results += vcc.log;
            int numResolvent = vcc.numUniqueResolventsFound;
            String nr = "Num Resolvents: " + numResolvent;
            if (proved == 0) {
                whyQuit += " Proved ";
            }
            else if (proved == 1) {
                whyQuit += " Timed Out. ";
                numUnproved++;
            }
            else {
                whyQuit += " Exhausted.  ";
                numUnproved++;
            }

            long endTime = System.nanoTime();
            long delayNS = endTime - startTime;
            long delayMS =
                    TimeUnit.MILLISECONDS
                            .convert(delayNS, TimeUnit.NANOSECONDS);
            summary +=
                    vcc.tag + whyQuit + " time: " + delayMS + " ms, " + nr
                            + "\n";
            vcc = null;
            if (myProverListener != null) {
                myProverListener.vcResult((proved == 0), myModels[i],
                        new Metrics(delayMS, myTimeout));
            }

            i++;
            csIt.remove();
            System.gc();

        }
        totalTime = System.currentTimeMillis() - totalTime;
        summary +=
                "Elapsed time from construction: " + totalTime + " ms" + "\n";
        String div = divLine("Summary");
        summary = div + summary + div;

        if (!m_environment.isWebIDEFlagSet()) {
            if (!FlagManager.getInstance().isFlagSet("nodebug")) {
                System.out.println(m_results + summary);
            }
            m_results = summary + m_results;

            outputProofFile();
        }
    }

    private String divLine(String label) {
        if (label.length() > 78) {
            label = label.substring(0, 77);
        }
        label = " " + label + " ";
        char[] div = new char[80];
        Arrays.fill(div, '=');
        int start = 40 - label.length() / 2;
        for (int i = start, j = 0; j < label.length(); ++i, ++j) {
            div[i] = label.charAt(j);
        }
        return new String(div) + "\n";
    }

    private String proofFileName() {
        File file = m_environment.getTargetFile();
        ModuleID cid = m_environment.getModuleID(file);
        file = m_environment.getFile(cid);
        String filename = file.toString();
        int temp = filename.indexOf(".");
        String tempfile = filename.substring(0, temp);
        String mainFileName;
        mainFileName = tempfile + ".cc.proof";
        return mainFileName;
    }

    private void outputProofFile() throws IOException {
        FileWriter w = new FileWriter(new File(proofFileName()));

        w.write("Proofs for " + m_scope.getModuleIdentifier() + " generated "
                + new Date() + "\n\n");

        w.write(m_results);
        w.write("\n");
        w.flush();
        w.close();
    }

}
