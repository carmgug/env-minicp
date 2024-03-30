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
import minicp.util.GraphUtil;
import minicp.util.GraphUtil.Graph;
import minicp.util.exception.InconsistencyException;
import minicp.util.exception.NotImplementedException;

import java.util.ArrayList;
import java.util.Arrays;

/**
 * Arc Consistent AllDifferent Constraint
 *
 * Algorithm described in
 * "A filtering algorithm for constraints of difference in CSPs" J-C. Régin, AAAI-94
 */
public class AllDifferentDC extends AbstractConstraint {

    private IntVar[] x;

    private final MaximumMatching maximumMatching;

    private final int nVar;
    private int nVal;

    // residual graph
    private ArrayList<Integer>[] in;
    private ArrayList<Integer>[] out;
    private int nNodes;
    protected Graph g = new Graph() {
        @Override
        public int n() {
            return nNodes;
        }

        @Override
        public Iterable<Integer> in(int idx) {
            return in[idx];
        }

        @Override
        public Iterable<Integer> out(int idx) {
            return out[idx];
        }
    };

    private int[] match;
    private boolean[] matched;

    private int minVal;
    private int maxVal;

    public AllDifferentDC(IntVar... x) {
        super(x[0].getSolver());
        this.x = x;
        maximumMatching = new MaximumMatching(x);
        match = new int[x.length];
        this.nVar = x.length;
    }

    @Override
    public void post() {
        for (int i = 0; i < nVar; i++) {
            x[i].propagateOnDomainChange(this);
        }
        updateRange();

        matched = new boolean[nVal];
        nNodes = nVar + nVal + 1;
        in = new ArrayList[nNodes];
        out = new ArrayList[nNodes];
        for (int i = 0; i < nNodes; i++) {
            in[i] = new ArrayList<>();
            out[i] = new ArrayList<>();
        }
        propagate();
    }

    private void updateRange() {
        minVal = Integer.MAX_VALUE;
        maxVal = Integer.MIN_VALUE;
        for (int i = 0; i < nVar; i++) {
            minVal = Math.min(minVal, x[i].min());
            maxVal = Math.max(maxVal, x[i].max());
        }
        nVal = maxVal - minVal + 1;
    }


    private void updateGraph() {
        nNodes = nVar + nVal + 1;
        int sink = nNodes - 1;
        for (int j = 0; j < nNodes; j++) {
            in[j].clear();
            out[j].clear();
        }
        for(int i=0;i<x.length;i++){
            int matched_value=match[i];
            int label= matched_value-minVal;
            matched[label]=true;

            int[] domain = new int[x[i].size()];
            x[i].fillArray(domain);
            for (int v:domain) {
                int node = i;
                int value_label = v+nVar-minVal;

                if(matched_value==v){

                    in[node].add(value_label);
                    out[value_label].add(node);

                }else{
                    in[value_label].add(node);
                    out[node].add(value_label);
                }
            }
        }

        //Arc from node to sink and from sink to node
        for(int v=minVal;v<=maxVal;v++){
            int value_node=v-minVal;
            if(matched[value_node]){
                int label_value_node=value_node+nVar;
                in[label_value_node].add(sink);
                out[sink].add(label_value_node);


            }else{
                //is a value node that is not matched
                //So we have an arc from value node to sink
                int label_value_node=v-minVal+nVar;
                in[sink].add(label_value_node);
                out[label_value_node].add(sink);

            }
        }
    }

    @Override
    public void propagate() {
        // TODO Implement the filtering
        // hint: use maximumMatching.compute(match) to update the maximum matching
        //       use updateRange() to update the range of values
        //       use updateGraph() to update the residual graph
        //       use  GraphUtil.stronglyConnectedComponents to compute SCC's
        matched = new boolean[nVal+nVar+1];

        maximumMatching.compute(match);
        updateRange();
        updateGraph();
        int[] scc = GraphUtil.stronglyConnectedComponents(g);
        for (int i=0;i<nVar;i++) {
            int matched_value=match[i];
            for(int v=x[i].min();v<=x[i].max();v++){
                int label_value_node=v-minVal+nVar;
                if(v!=matched_value && scc[i]!=scc[label_value_node]){
                    x[i].remove(v);
                }
            }
        }


    }
}
