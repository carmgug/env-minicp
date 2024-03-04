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

import minicp.engine.core.AbstractConstraint;
import minicp.engine.core.IntVar;
import minicp.util.exception.NotImplementedException;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

public class Element1DVar extends AbstractConstraint {

    private final IntVar[] array;
    private final IntVar y;
    private final IntVar z;

    

    public Element1DVar(IntVar[] array, IntVar y, IntVar z) {
        super(y.getSolver());
        this.array = array;
        this.y = y;
        this.z = z;

        
    }

    @Override
    public void post() {

        y.removeBelow(0);
        y.removeAbove(array.length-1);
        y.propagateOnDomainChange(this);
        for(IntVar v:array){
            v.propagateOnDomainChange(this);
        }
        z.propagateOnDomainChange(this);
        propagate();
    }

    @Override
    public void propagate() {



        int[] values=new int[y.size()];
        int size = y.fillArray(values);
        for (int i = 0 ; i < size ; i++) {
            int valueOfY = values[i];
            int[] valuesOfT=new int[array[valueOfY].size()];
            int size_v = array[valueOfY].fillArray(valuesOfT);
            boolean remove=true;
            for(int v:valuesOfT){
                if(z.contains(v)){ //D(T[i]) intersect D(z) != empty_set
                    remove=false;
                }
            }
            if(remove) y.remove(valueOfY);

        }

        int[] z_values=new int[z.size()];
        int z_size = z.fillArray(z_values);
        for (int i = 0 ; i < z_size ; i++) {
            int valueOfZ = z_values[i];
            boolean remove=true;
            for (int j = 0 ; j < size ; j++) {
                int valueOfY = values[j];
                if(array[valueOfY].contains(valueOfZ)){
                    remove=false;
                    break;
                }
            }
            if(remove){
                z.remove(valueOfZ);
            }
        }
        //Filter T
        if(y.isFixed()){
            y.getSolver().post(new Equal(z,array[y.min()]));
            setActive(false);
        }

    }

    

}
