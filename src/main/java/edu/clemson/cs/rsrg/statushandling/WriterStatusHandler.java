/**
 * WriterStatusHandler.java
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
package edu.clemson.cs.rsrg.statushandling;

import edu.clemson.cs.rsrg.parsing.data.Location;
import java.io.IOException;
import java.io.Writer;

/**
 * <p>This class outputs all debugging, errors and/or
 * other information coming from the compiler to the specified
 * writer.</p>
 *
 * @author Yu-Shan Sun
 * @version 1.0
 */
public class WriterStatusHandler implements StatusHandler {

    // ===========================================================
    // Member Fields
    // ===========================================================

    /** <p>This is the output writer object.</p> */
    private final Writer myOutputWriter;

    /** <p>Boolean flag to check to see if we are still logging.</p> */
    protected boolean stopLogging;

    // ===========================================================
    // Constructors
    // ===========================================================

    /**
     * <p>This constructor takes a Java <code>Writer</code> object
     * that will be used to display the information.</p>
     *
     * @param outWriter A <code>Writer</code> object.
     */
    public WriterStatusHandler(Writer outWriter) {
        myOutputWriter = outWriter;
        stopLogging = false;
    }

    // ===========================================================
    // Public Methods
    // ===========================================================

    /**
     * <p>Outputs a critical error message.</p>
     *
     * @param l The location where we encountered the error.
     * @param msg Message to be displayed.
     */
    public final void error(Location l, String msg) {
        try {
            if (!stopLogging) {
                StringBuilder sb = new StringBuilder();
                sb.append("\nError: ");
                if (l != null) {
                    sb.append(l.toString());
                }
                sb.append("\n\n");
                sb.append("\t");
                sb.append(msg);
                sb.append("\n\n");

                myOutputWriter.write(sb.toString());
                myOutputWriter.flush();
            }
            else {
                throw new RuntimeException("Error handler has been stopped.");
            }
        }
        catch (IOException e) {
            System.err
                    .println("Error writing information to the specified output.");
            e.printStackTrace();
        }
    }

    /**
     * <p>Checks to see if we are still logging information.</p>
     *
     * @return True if we are done logging, false otherwise.
     */
    public final boolean hasStopped() {
        return stopLogging;
    }

    /**
     * <p>Outputs an informational message, not an error or warning.</p>
     *
     * @param l The location where we encountered the error.
     * @param msg A compilation message.
     */
    public final void info(Location l, String msg) {
        try {
            if (!stopLogging) {
                StringBuilder sb = new StringBuilder();
                if (l != null) {
                    sb.append(l.toString());
                }
                sb.append(msg);
                sb.append("\n");

                myOutputWriter.write(sb.toString());
                myOutputWriter.flush();
            }
            else {
                throw new RuntimeException("Error handler has been stopped.");
            }
        }
        catch (IOException e) {
            System.err
                    .println("Error writing information to the specified output.");
            e.printStackTrace();
        }
    }

    /**
     * <p>Stop logging anymore information.
     *
     * (Note: Should only be called when the compile process
     * is over or has been aborted due to an error.)</p>
     */
    public void stopLogging() {
        stopLogging = true;

        try {
            myOutputWriter.close();
        }
        catch (IOException e) {
            System.err.println("Error closing the output stream.");
            e.printStackTrace();
        }
    }

    /**
     * <p>Outputs a warning message.</p>
     *
     * @param l The location where we encountered the error.
     * @param msg Message to be displayed.
     */
    public final void warning(Location l, String msg) {
        try {
            if (!stopLogging) {
                StringBuilder sb = new StringBuilder();
                sb.append("\nWarning: ");
                if (l != null) {
                    sb.append(l.toString());
                }
                sb.append("\n");
                sb.append(msg);
                sb.append("\n");

                myOutputWriter.write(sb.toString());
                myOutputWriter.flush();
            }
            else {
                throw new RuntimeException("Error handler has been stopped.");
            }
        }
        catch (IOException e) {
            System.err
                    .println("Error writing information to the specified output.");
            e.printStackTrace();
        }
    }

}