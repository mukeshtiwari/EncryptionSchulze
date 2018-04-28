/* 
 * The contents of this file is dual-licensed under 2 
 * alternative Open Source/Free licenses: LGPL 2.1 or later and 
 * Apache License 2.0. (starting with JNA version 4.0.0).
 * 
 * You can freely decide which license you want to apply to 
 * the project.
 * 
 * You may obtain a copy of the LGPL License at:
 * 
 * http://www.gnu.org/licenses/licenses.html
 * 
 * A copy is also included in the downloadable source code package
 * containing JNA, in file "LGPL2.1".
 * 
 * You may obtain a copy of the Apache License at:
 * 
 * http://www.apache.org/licenses/
 * 
 * A copy is also included in the downloadable source code package
 * containing JNA, in file "AL2.0".
 */
package com.sun.jna;

import junit.framework.TestCase;

public class HeadlessLoadLibraryTest extends TestCase {
    
    public void testLoadWhenHeadless() {
        System.setProperty("java.awt.headless", "true");
        assertTrue("Pointer size must not be zero", Pointer.SIZE > 0);
    }
    
    public static void main(String[] args) {
        junit.textui.TestRunner.run(HeadlessLoadLibraryTest.class);
    }
}