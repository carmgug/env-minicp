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
import minicp.state.StateInt;
import minicp.util.exception.InconsistencyException;
import minicp.util.exception.NotImplementedException;

import java.util.LinkedList;
import java.util.stream.IntStream;

/**
 * Forward Checking filtering AllDifferent Constraint
 *
 * Whenever one variable is fixed, this value
 * is removed from the domain of other variables.
 * This filtering is weaker than the {@link AllDifferentDC}
 * but executes faster.
 */
public class AllDifferentFWC extends AbstractConstraint {

    private IntVar[] x;
    private int[] fixed;
    private StateInt nFixed;

    public AllDifferentFWC(IntVar... x) {
        super(x[0].getSolver());
        this.x = x;
        int n=this.x.length;
        nFixed=getSolver().getStateManager().makeStateInt(0);
        fixed=IntStream.range(0,n).toArray();
    }

    @Override
    public void post() {
        for (IntVar var : x)
            var.propagateOnDomainChange(this);
        propagate();
    }

    @Override
    public void propagate() {
        // TODO use the sparse-set trick as seen in Sum.java
        // Filter the unfixed vars and update the partial sum
        int nF = nFixed.value();
        // iterate over not-fixed variables
        // if  one variable is detected as fixed
        for (int i = nF; i < x.length; i++) {
            int idx = fixed[i]; //variabile corrente
            IntVar y= x[idx];
            if (x[idx].isFixed()) {
                // iterate over not-fixed variables
                for (int j = nF; j < x.length; j++) {
                    int unfixed_idx = fixed[j];
                    if(unfixed_idx==idx) continue;
                    x[unfixed_idx].remove(y.min());
                }
                fixed[i] = fixed[nF]; // Swap the variables
                fixed[nF] = idx;
                nF++;
            }
        }
        nFixed.setValue(nF);

    }
}
