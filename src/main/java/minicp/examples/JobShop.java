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

package minicp.examples;

import minicp.engine.constraints.Disjunctive;
import minicp.engine.constraints.DisjunctiveBinary;
import minicp.engine.core.IntVar;
import minicp.engine.core.Solver;
import minicp.search.SearchStatistics;
import minicp.util.Procedure;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Optional;
import java.util.function.Supplier;

import static minicp.cp.BranchingScheme.*;
import static minicp.cp.Factory.*;

/**
 * The JobShop Problem.
 * <a href="https://en.wikipedia.org/wiki/Job_shop_scheduling">Wikipedia.</a>
 */
public class JobShop extends OptimizationProblem {

    JobShopInstance instance;
    Solver cp;
    IntVar[][] start;
    IntVar[][] end;
    IntVar[] endLast;
    IntVar makespan;

    public JobShop(String instancePath) {
        instance = new JobShopInstance(instancePath);
    }

    public static IntVar[] flatten(IntVar[][] x) {
        return Arrays.stream(x).flatMap(Arrays::stream).toArray(IntVar[]::new);
    }

    @Override
    public void buildModel() {
        cp = makeSolver();

        start = new IntVar[instance.nJobs][instance.nMachines];
        end = new IntVar[instance.nJobs][instance.nMachines];

        // variable creation
        for (int i = 0; i < instance.nJobs; i++) {
            for (int j = 0; j < instance.nMachines; j++) {
                start[i][j] = makeIntVar(cp, 0, instance.horizon);
                end[i][j] = plus(start[i][j], instance.duration[i][j]);
            }
        }

        // job precedences
        for (int i = 0; i < instance.nJobs; i++) {
            for (int j = 1; j < instance.nMachines; j++) {
                cp.post(lessOrEqual(end[i][j - 1], start[i][j]));
            }
        }

        // All disjunctive binary constraints (useful for custom search)
        ArrayList<DisjunctiveBinary> disjunctiveBinaries = new ArrayList<>();

        for (int m = 0; m < instance.nMachines; m++) {
            // collect activities on machine m
            IntVar[] start_m = instance.collect(start, m);
            int[] dur_m = instance.collect(instance.duration, m);

            // TODO 1: for each pair of activities a1, a2 on machine m post a DisjunctiveBinary
            //       and add the constraint to the disjunctiveBinaries collection
            for (int i = 0; i < start_m.length; i++) {
                for (int j = i + 1; j < start_m.length; j++) {
                    DisjunctiveBinary disjunctiveBinary = new DisjunctiveBinary(start_m[i], dur_m[i], start_m[j], dur_m[j]);
                    cp.post(disjunctiveBinary);
                    disjunctiveBinaries.add(disjunctiveBinary);
                }
            }
            // Global constraint (the ones using theta-trees)
            // By default, until you have implemented the advanced
            // filtering, it only posts a cumulative with capacity 1
            cp.post(new Disjunctive(start_m, dur_m));
        }


        // objective = makespan minimization
        endLast = new IntVar[instance.nJobs];
        for (int i = 0; i < instance.nJobs; i++) {
            endLast[i] = end[i][instance.nMachines - 1];
        }
        makespan = maximum(endLast); // makespan = the maximum of the last task of each job
        objective = cp.minimize(makespan);


        // Search to fix the start time of all activities

        Supplier<Procedure[]> branchStart = firstFail(flatten(start));
        //dfs = makeDfs(cp, branchStart);


        // TODO 2: Replace the search by fixing the precedence relation of
        //  each binary constraint, then fix the makespan variable to its minimum value
        Supplier<Procedure[]> fixMakespan = () -> makespan.isFixed() ? EMPTY : new Procedure[] {() -> cp.post(equal(makespan,makespan.min()))};
        //  HINT: use a and combinator makeDfs(cp, and(branchPrecedences, fixMakespan));
        //        where branchPrecedences is in charge of fixing the precedences
        Supplier<Procedure[]> branchPrecedences = () -> {
            //Select first the machine m that has the smallest
            // sum of size of the domains of the activities to be executed on it
            int selected_machine=selectMachine();
            if(selected_machine==-1) return EMPTY;
            int[] selected_activities=selectActivities_ij(selected_machine);
            if(selected_activities[0]==-1 && selected_activities[1]==-1) return EMPTY;
            int activity_i=selected_activities[0];
            int activity_j=selected_activities[1];
            //branch on bij=true i start before j
            //branch on bij=false j start before i
            DisjunctiveBinary constraint_ij=disjunctiveBinaries.get(activity_i+activity_j);

            int slackJifIStartBeforeJ=constraint_ij.slackIfBefore();
            int slackIifJStartBeforeI=constraint_ij.slackIfAfter();
            if(slackJifIStartBeforeJ>slackIifJStartBeforeI){
                return branch(() -> constraint_ij.before().fix(true),
                        () -> constraint_ij.before().fix(false));
            }
            else{
                return branch(() -> constraint_ij.before().fix(false),
                        () -> constraint_ij.before().fix(true));
            }
        };
        dfs=makeDfs(cp,and(branchPrecedences,fixMakespan));


    }
    //select the pair of activities (i,j) that will be executed on machine m
    //with the minimium start(i).size()*start(j).size()
    private int[] selectActivities_ij(int machine){
        int[] selected_ij={-1,-1};
        int minDotSize=Integer.MAX_VALUE;
        for(int i=0;i<instance.nJobs;i++){
            if(start[i][machine].isFixed()) continue;
            for(int j=i+1;j<instance.nJobs;j++){
                if(start[j][machine].isFixed()) continue;
                if(start[i][machine].size()*start[j][machine].size()<minDotSize){
                    minDotSize=start[i][machine].size()*start[j][machine].size();
                    selected_ij[0]=i;
                    selected_ij[1]=j;
                }
            }
        }
        return selected_ij;
    }

    private int selectMachine() {
        int m = -1;
        int minSize = Integer.MAX_VALUE;
        for (int curr_machine = 0; curr_machine < instance.nMachines; curr_machine++) {
            int size = 0;
            //Iterate on the set of activities executed on machine j
            //m that contains at least one non-fixed start(i)
            for (int i = 0; i < instance.nJobs; i++) {
                if(start[i][curr_machine].isFixed()) continue;
                //start[i][j] is the start time domain of job i on machine j
                size += start[i][curr_machine].size();
            }
            if(size==0){
                //The machine not contain at least one non-fixed start(i)
                continue;
            }
            else if (size < minSize) {
                minSize = size;
                m = curr_machine;
            }
        }
        return m;
    }

    public static void main(String[] args) {
        // this instance is quite hard to solve with the given model
        // but with all the new ingredients you will add to improve the model,
        // you should be able to find and prove the optimal solution in a few seconds
        JobShop jb = new JobShop("data/jobshop/uclouvain.txt");
        jb.buildModel();
        SearchStatistics statistics = jb.solve(true);
        System.out.println(statistics);
    }
}

