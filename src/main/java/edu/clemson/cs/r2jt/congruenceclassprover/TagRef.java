/**
 * TagRef.java
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

/**
 * Created by Mike on 9/9/2016.
 */
public class TagRef {

    private String m_tag;
    private int m_ref;

    public TagRef(String tag, int ref) {
        m_ref = ref;
        m_tag = tag;
    }

    public String getTag() {
        return m_tag;
    };

}
