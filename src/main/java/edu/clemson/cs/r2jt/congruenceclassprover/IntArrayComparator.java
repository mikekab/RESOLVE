/**
 * IntArrayComparator.java
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

import java.util.Comparator;

/**
 * Created by Mike on 10/18/2016.
 */
public class IntArrayComparator implements Comparator<int[]> {

    public int compare(int[] a, int[] b) {
        if (a.length != b.length) {
            return a.length - b.length;
        }
        for (int i = 0; i < a.length; ++i) {
            if (a[i] != b[i]) {
                return a[i] - b[i];
            }
        }
        return 0;
    }

}
