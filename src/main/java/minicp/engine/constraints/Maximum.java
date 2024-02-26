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

import java.util.Arrays;

/**
 * Maximum Constraint
 */
public class Maximum extends AbstractConstraint {

    private final IntVar[] x;
    private final IntVar y;

    /**
     * Creates the maximum constraint y = maximum(x[0],x[1],...,x[n])?
     *
     * @param x the variable on which the maximum is to be found
     * @param y the variable that is equal to the maximum on x
     */
    public Maximum(IntVar[] x, IntVar y) {
        super(x[0].getSolver());
        assert (x.length > 0);
        this.x = x;
        this.y = y;

    }


    @Override
    public void post() {
        propagate();

        for(IntVar var:x){
            var.propagateOnBoundChange(this);
        }
        y.propagateOnBoundChange(this);


    }



    @Override
    public void propagate() {
        int max=Integer.MIN_VALUE;
        int count_x_intersect_y=0; //Numero di variabili che si sovrappongono a y
        int idx_intersect_y=-1; //Indice dell'ultima variabile che si sovrappone a y

        for(int i=0;i<x.length;i++){
            x[i].removeAbove(y.max()); //Rimuoviamo i valori che sono maggiori di Y
            max=Math.max(x[i].max(),max); //Teniamo traccia del massimo corrente
            y.removeBelow(x[i].min()); //Rimuoviamo i valori di y che sono minori di del minimo di x
            if(x[i].max()>=y.min()){
                count_x_intersect_y++;
                idx_intersect_y=i;
            }
        }
        if(count_x_intersect_y==1){
            x[idx_intersect_y].removeBelow(y.min());
        }

        y.removeAbove(max);







    }
}
