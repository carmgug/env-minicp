/*
 * mini-cp is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License  v3
 * as published by the Free Software Foundation.
 *
 * mini-cp is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY.
 * See the GNU Lesser General Public License  for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with mini-cp. If not, see http://www.gnu.org/licenses/lgpl-3.0.en.html
 *
 * Copyright (c)  2018. by Laurent Michel, Pierre Schaus, Pascal Van Hentenryck
 */


package minicp.engine.constraints;

import minicp.cp.Factory;
import minicp.engine.core.AbstractConstraint;
import minicp.engine.core.Constraint;
import minicp.engine.core.IntVar;
import minicp.util.exception.NotImplementedException;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;


/**
 *
 * Element Constraint modeling {@code array[y] = z}
 *
 */
public class Element1DDomainConsistent extends AbstractConstraint {

    private final int[] t;
    private final IntVar y;
    private final IntVar z;

    /**
     * Creates an element constraint {@code array[y] = z}
     *
     * @param array the array to index
     * @param y the index variable
     * @param z the result variable
     */
    public Element1DDomainConsistent(int[] array, IntVar y, IntVar z) {
        super(y.getSolver());
        this.t = array;
        this.y = y;
        this.z = z;
    }

    @Override
    public void post() {
        y.removeBelow(0);
        y.removeAbove(t.length-1);
        y.propagateOnDomainChange(this);
        z.propagateOnDomainChange(this);
        propagate();
    }

    public void propagate(){
        int[] values=new int[y.size()];
        int size = y.fillArray(values);

        for (int i = 0 ; i < size ; i++) {
            int valueOfY = values[i];
            if(!z.contains(t[valueOfY])){
                y.remove(valueOfY);
            }
        }

        int[] z_values=new int[z.size()];
        int z_size = z.fillArray(z_values);
        for (int i = 0 ; i < z_size ; i++) {
            int valueOfZ = z_values[i];
            int zSup=0;
            for (int j = 0 ; j < size ; j++) {
                int valueOfY = values[j];
                if(t[valueOfY]==valueOfZ){
                    zSup++;
                }
            }
            if(zSup==0){
                z.remove(valueOfZ);
            }
        }




    }
}
