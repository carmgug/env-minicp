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
import minicp.engine.core.BoolVar;
import minicp.engine.core.IntVar;
import minicp.util.exception.InconsistencyException;
import minicp.util.exception.NotImplementedException;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;

import static minicp.cp.Factory.*;

/**
 * Disjunctive Scheduling Constraint:
 * Any two pairs of activities cannot overlap in time.
 */
public class Disjunctive extends AbstractConstraint {

    private final IntVar[] start;
    private final int[] duration;
    private final IntVar[] end;

    private final boolean postMirror;

    private final Integer[] permLct;
    private final Integer[] permEst;
    private final int[] rankEst;
    private final int[] startMin;
    private final int[] endMax;

    private final ThetaTree thetaTree;

    /**
     * Creates a disjunctive constraint that enforces
     * that for any two pair i,j of activities we have
     * {@code start[i]+duration[i] <= start[j] or start[j]+duration[j] <= start[i]}.
     *
     * @param start the start times of the activities
     * @param duration the durations of the activities
     */
    public Disjunctive(IntVar[] start, int[] duration) {
        this(start, duration, true);
    }


    private Disjunctive(IntVar[] start, int[] duration, boolean postMirror) {
        super(start[0].getSolver());
        this.start = start;
        this.duration = duration;
        this.end = Factory.makeIntVarArray(start.length, i -> plus(start[i], duration[i]));
        this.postMirror = postMirror;

        startMin = new int[start.length];
        endMax = new int[start.length];
        permEst = new Integer[start.length];
        permLct = new Integer[start.length];
        rankEst = new int[start.length];
        for (int i = 0; i < start.length; i++) {
            permEst[i] = i;
            permLct[i] = i;
        }
        thetaTree = new ThetaTree(start.length);
        
    }
    @Override
    public void post() {

        /*
        int[] demands = new int[start.length];
        for (int i = 0; i < start.length; i++) {
            demands[i] = 1;
        }

        getSolver().post(new Cumulative(start, duration, demands, 1), false);

         */

        for (int i = 0; i < start.length; i++) {
            start[i].propagateOnDomainChange(this);
        }





        // TODO 1: replace by posting binary decomposition (DisjunctiveBinary) using IsLessOrEqualVar
        for (int i = 0; i < start.length; i++) {
            for (int j = i+1; j < start.length; j++) {
                getSolver().post(new DisjunctiveBinary(start[i], duration[i], start[j], duration[j]),false);
            }
        }

        // TODO 2: add the mirror filtering as done in the Cumulative Constraint
        if (postMirror) {
            IntVar[] startMirror = Factory.makeIntVarArray(start.length, i -> minus(end[i]));
            getSolver().post(new Disjunctive(startMirror, duration, false), false);
        }

        for (int i = 0; i < start.length; i++) {
            start[i].propagateOnBoundChange(this);
        }


        propagate();

    }


    @Override
    public void propagate() {
        // HINT: for the TODO 3-6 you'll need the ThetaTree data-structure

        // TODO 3: read and understand the OverLoadCheck algorithm implementation


        // TODO 4: add the Detectable Precedences algorithm

        // TODO 5: add the Not-Last algorithm

        // TODO 6 (optional): implement the Lambda-Theta tree and implement the Edge-Finding

        boolean changed = true;
        while (changed) {
            overLoadChecker();
            changed = detectablePrecedence();
            // Java has short-circuit evaluation: notLast will only be called if changed is false.
            changed = changed || notLast();
        }

    }

    private void update() {
        Arrays.sort(permEst, Comparator.comparingInt(i -> start[i].min()));
        for (int i = 0; i < start.length; i++) {
            rankEst[permEst[i]]=i;
            startMin[i] = start[i].min();
            endMax[i] = end[i].max();
        }
    }

    public void overLoadChecker() {
        update();
        Arrays.sort(permLct, Comparator.comparingInt(i -> end[i].max()));
        thetaTree.reset();
        for (int i = 0; i < start.length; i++) {
            int activity = permLct[i];
            thetaTree.insert(rankEst[activity], end[activity].min(), duration[activity]);
            if (thetaTree.getECT() > end[activity].max()) {
                throw new InconsistencyException();
            }
        }
    }

    private Integer[] getIndexOfActivities(){
        Integer[] idxs= new Integer[start.length];
        for (int i = 0; i < start.length; i++) {
            idxs[i] = i;
        }
        return idxs;
    }


    /**
     * @return true if one domain was changed by the detectable precedence algo
     */
    public boolean detectablePrecedence() {
        update();

        //Index of the activities sorted by lct-duration
        Integer[] permLst= getIndexOfActivities();
        Arrays.sort(permLst, Comparator.comparingInt(i -> start[i].max()));

        //Index of the activities sorted by earliest start time+duration
        Integer[] permEct = getIndexOfActivities();
        Arrays.sort(permEct, Comparator.comparingInt(i -> start[i].min()+duration[i]));
        boolean change = false;


        //implements detectablePrecedence
        Iterator<Integer> it=Arrays.asList(permLst).iterator();
        int pos_j=0;
        int activity_j=it.next();
        thetaTree.reset();
        int[] estPrime = new int[start.length];
        int pos_i=0;

        boolean[] inserted_activities=new boolean[start.length];
        for(int i=0;i<start.length;i++) {
            int activity=permEct[i];
            inserted_activities[activity]=false;
        }

        for(int activity_i:permEct){
            int est_i=end[activity_i].min()-duration[activity_i];
            int p_i=duration[activity_i];
            int lct_j=end[activity_j].max();
            int duration_j=duration[activity_j];

            while(est_i+p_i>lct_j-duration_j){
                thetaTree.insert(rankEst[activity_j], end[activity_j].min(), duration[activity_j]);
                inserted_activities[activity_j]=true;
                if(it.hasNext()) activity_j=it.next();
                else break;
                lct_j=end[activity_j].max();
                duration_j=duration[activity_j];
                pos_j++;
            }

            if(inserted_activities[activity_i]){
                thetaTree.remove(rankEst[activity_i]);
            }
            int ect_theta_i=thetaTree.getECT();
            estPrime[activity_i]=Math.max(est_i,ect_theta_i);
            if(inserted_activities[activity_i]) thetaTree.insert(rankEst[activity_i],end[activity_i].min(),duration[activity_i]);

            pos_i++;
        }
        for(int i=0;i<start.length;i++){
            //early start time of activity i is equal to estPrime[i]
            int activity_i=permEct[i];
            int size=end[activity_i].size();
            end[activity_i].removeBelow(estPrime[activity_i]+duration[activity_i]);
            if(size!=end[activity_i].size()){
                change=true;
            }
        }
        return change;
    }

    /**
     * @return true if one domain was changed by the not-last algo
     */
    public boolean notLast() {
        update();
        Integer[] permLst= getIndexOfActivities();
        //Activities sorted by Last starting Time
        Arrays.sort(permLst, Comparator.comparingInt(i -> start[i].max()));

        //Activities sorted by Last completion time
        Integer[] permLct= getIndexOfActivities();
        Arrays.sort(permLct, Comparator.comparingInt(i -> start[i].max()+duration[i]));

        boolean change = false;

        Iterator<Integer> ite=Arrays.asList(permLst).iterator();
        int pos_k=0;
        int activity_k=ite.next();
        int activity_j=-1;
        thetaTree.reset();

        Integer[] lctPrime = new Integer[start.length];
        boolean[] inserted_activities=new boolean[start.length];
        for (int i = 0;i<start.length;i++) {
            int activity_i = permLct[i];
            lctPrime[activity_i] = start[activity_i].max()+duration[activity_i];
            inserted_activities[activity_i]=false;
        }

        int pos_i=0;
        for(Integer activity_i:permLct){
            int lct_i=end[activity_i].max();
            int lct_k=end[activity_k].max();
            int duration_k=duration[activity_k];
            int duration_i=duration[activity_i];

            while(lct_i>lct_k-duration_k){
                thetaTree.insert(rankEst[activity_k],end[activity_k].min(), duration_k);
                inserted_activities[activity_k]=true;
                activity_j=activity_k;
                if(ite.hasNext()) {
                    activity_k = ite.next();
                }
                else { break;}
                lct_k=end[activity_k].max();
                duration_k=duration[activity_k];
                pos_k++;
            }

            if(inserted_activities[activity_i]) thetaTree.remove(rankEst[activity_i]);
            int ect_theta_i=thetaTree.getECT();

            if(ect_theta_i>lct_i-duration_i){
                int lct_j=end[activity_j].max();
                int duration_j=duration[activity_j];
                lctPrime[activity_i]=Math.min(lct_i,lct_j-duration_j);
            }
            if(inserted_activities[activity_i]) thetaTree.insert(rankEst[activity_i],end[activity_i].min(),duration[activity_i]);
            pos_i++;

        }

        for(int i=0;i<start.length;i++){
            int activity_i=permLct[i];
            int size=end[activity_i].size();
            end[activity_i].removeAbove(lctPrime[activity_i]);
            if(size!=end[activity_i].size()){
                change=true;
            }
        }
        return change;
    }
}
