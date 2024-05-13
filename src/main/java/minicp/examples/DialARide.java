package minicp.examples;

import minicp.engine.constraints.*;
import minicp.engine.core.IntVar;
import minicp.engine.core.Solver;
import minicp.search.DFSearch;
import minicp.search.Objective;
import minicp.util.exception.InconsistencyException;
import minicp.util.io.InputReader;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static minicp.cp.BranchingScheme.*;
import static minicp.cp.Factory.*;


import java.lang.management.ManagementFactory;

public class DialARide {

    final int nVehicles;
    final int maxRouteDuration;
    final int vehicleCapacity;
    final int maxRideTime;
    final ArrayList<RideStop> pickupRideStops;
    final ArrayList<RideStop> dropRideStops;
    final RideStop depot;
    final int[][] distanceMatrix;
    final ArrayList<RideStop> pickupAndDropRideStops;
    final int number_of_start_depots; //A depot for each vehicle
    final int number_of_end_depots; // A end depot for each vehicles
    final int number_of_tasks;
    final int n ;
    final int first_end_depot ;

    private Solver cp;
    private IntVar[] succ;
    private IntVar[] pred;
    private IntVar[] distSucc;
    private IntVar[] distPred;
    private IntVar[] time;
    private IntVar[] peopleOn;
    private IntVar[] index;
    private IntVar[] visitedByVehicle;

    //i is the task
    private IntVar[] managedBy;

    private IntVar totalDist;
    private Objective obj_function;
    AtomicInteger weight_distance= new AtomicInteger(1);
    AtomicInteger lns_started= new AtomicInteger(0);




    private double getDistanceWeight() {
        if(lns_started.get()==0){
            return 0.3;
        }
        else {
            return 0.4;
        }
    }

    private double getTimeWeight() {
        if(lns_started.get()==0){
            return 0.7;
        }
        else {
            return 0.6;
        }
    }
    private double dropWeight() {
        if(lns_started.get()==0){
            return 0.3;
        }
        else {
            return 0.9;
        }
    }




    public DialARide (int nVehicles, int maxRouteDuration, int vehicleCapacity,
                      int maxRideTime, ArrayList<RideStop> pickupRideStops, ArrayList<RideStop> dropRideStops,
                      RideStop depot) {
        this.nVehicles = nVehicles;
        this.maxRouteDuration = maxRouteDuration;
        this.vehicleCapacity = vehicleCapacity;
        this.maxRideTime = maxRideTime;
        this.pickupRideStops = pickupRideStops;
        this.dropRideStops = dropRideStops;
        this.depot = depot;

        this.number_of_start_depots = nVehicles; //A depot for each vehicle
        this.number_of_end_depots= nVehicles; // A end depot for each vehicles
        this.number_of_tasks = pickupRideStops.size();
        this.n = (number_of_tasks*2) + nVehicles + nVehicles;
        this.first_end_depot = nVehicles+(number_of_tasks*2);

        this.distanceMatrix = new int[n][n];
        this.pickupAndDropRideStops = new ArrayList<>();
        buildPickUpAndDrop(pickupAndDropRideStops,pickupRideStops,dropRideStops,depot,number_of_end_depots,maxRouteDuration);
        computeDistanceMatrix(distanceMatrix,nVehicles,number_of_tasks,pickupAndDropRideStops,depot);

    }

    public void buildModel(){
        //Intizialization of variables
        cp = makeSolver();
        //Create Variables
        succ = makeIntVarArray(cp, n, n); //succ[i] is the successor node of i
        pred = makeIntVarArray(cp,n,n); //pred[i] is the predecessor node of i
        distSucc = makeIntVarArray(cp, n, 0, maxRideTime+1); //distSucc[i] is the distance between node i and its successor
        distPred = makeIntVarArray(cp, n, 0, maxRideTime+1); //distPred[i] is the distance between node i and its predecessor
        peopleOn = makeIntVarArray(cp, n, vehicleCapacity+1); //peopleOn[i] is the number of people on the vehicle when it visit the node i
        index = makeIntVarArray(cp, n, n); //index[i] is the position of the node i in the path (so index[i]=i)
        visitedByVehicle = makeIntVarArray(cp, n, nVehicles); //VisitedByVehicle[i] is the vehicle that visit the node i
        managedBy= makeIntVarArray(cp,number_of_tasks,nVehicles); //IntVar that represent the vehicle that manage the pickup node i
        time = makeIntVarArray(cp, n, 0, maxRouteDuration+1); //time[i] is the time when the vehicle visit the n

        //Adding circuit constraint
        cp.post(new Circuit(succ));
        cp.post(new Circuit(pred));

        //Channelling between pred and succ
        for (int i = 0; i < n; i++) {
            cp.post(new Element1DVar(pred, succ[i],index[i]));
            cp.post(new Element1DVar(succ,pred[i],index[i]));
        }

        //vehicleCapacity maximum value
        for (int i = 0; i < n; i++) {
            cp.post(lessOrEqual(peopleOn[i],vehicleCapacity));
            //cp.post(largerOrEqual(peopleOn[i],0)); //the veichle capacity must be at least 0
        }


        //Manage Time PeopleOn VisitByVehicle at Start and at the End
        //Departure time from the depots
        for (int i = 0; i < nVehicles; i++) {
            int start_depot=i;
            int end_depot=nVehicles+number_of_tasks*2+i;

            //Manage of the time at start and depot
            //Start
            cp.post(equal(time[start_depot],0)); //the time at start depot is 0
            //update time
            cp.post(new Element1DVar(time, succ[i],sum(time[i],distSucc[i])));


            //End
            cp.post(lessOrEqual(time[end_depot], maxRouteDuration)); //the time at end depot is less than the maxRouteDuration

            //Manage people at start and end depot
            //Start depot
            cp.post(equal(peopleOn[start_depot],0)); //people on start depot is 0
            //End depot
            cp.post(equal(peopleOn[end_depot], 0));
            //the pred of the end depot must have 0 people on
            cp.post(new Element1DVar(peopleOn,pred[end_depot],peopleOn[end_depot]));

            //Manage the successor and the predecessor at start and end depot
            //Start depot
            cp.post(equal(pred[(start_depot + 1) % nVehicles], end_depot));

            // The successor of the start depot can only be a pickup node
            for (int dropNode = nVehicles+number_of_tasks; dropNode < n-nVehicles ; dropNode++) {
                cp.post(notEqual(succ[i],dropNode));
            }
            //End depot
            //Manage the end depot
            cp.post(equal(succ[end_depot], (start_depot + 1) % nVehicles));
            //The pred of the end depot must have the same vehicle
            cp.post(new Element1DVar(visitedByVehicle,pred[end_depot],visitedByVehicle[end_depot]));
            //the pred of the end depot couldnt be a pickup
            for (int pickup = nVehicles; pickup < nVehicles+number_of_tasks; pickup++) {
                cp.post(notEqual(pred[end_depot],pickup));
            }

            //Manage vehicle that visit the depot
            //Start
            cp.post(equal(visitedByVehicle[start_depot],i)); //start depot 0 is visited by i
            //update visitedByVehicle
            cp.post(new Element1DVar(visitedByVehicle, succ[start_depot],visitedByVehicle[start_depot]));
            //End
            //The vehicle that visit the end depot is the same that visit the start depot
            cp.post(equal(visitedByVehicle[start_depot],visitedByVehicle[end_depot]));

            //Manage distance
            //Start
            //update distance from the successor
            cp.post(new Element1D(distanceMatrix[i], succ[i],distSucc[i]));
            //The distance between the start depot and the predecessor is 0
            cp.post(equal(distPred[start_depot],0));
            //End
            //update distance from the predecessor
            cp.post(new Element1D(distanceMatrix[end_depot], pred[end_depot],distPred[end_depot]));
            //the distance between the end depot and the successor is 0
            cp.post(equal(distSucc[end_depot],0));

        }

        // 2.5 Time PeopleOn VisitByVehicle at the Pickup and Drop nodes
        for (int i = nVehicles; i <nVehicles+number_of_tasks; i++) {
            int task_id = i - nVehicles;
            int pickup = i;
            int drop = i + number_of_tasks;


            //Update distance and time from successor
            cp.post(new Element1D(distanceMatrix[pickup], succ[pickup], distSucc[pickup]));
            cp.post(new Element1DVar(time, succ[pickup], sum(time[pickup], distSucc[pickup])));

            //Update distance from predecessor
            cp.post(new Element1D(distanceMatrix[pickup],pred[pickup],distPred[pickup]));


            //Manage Time
            //The vehicle must arrive at the pickup node before the end of the route
            cp.post(lessOrEqual(time[pickup], maxRouteDuration));
            //The vehicle must arrive at the pickup node before the end of the time window
            cp.post(lessOrEqual(time[pickup], pickupRideStops.get(task_id).window_end));
            //The vehicle must arrive at the pickup node before the end of the rideTime
            //time[pickup]>=time[drop]-maxRideTime becuase time[drop] need to end before time[pickup]+maxRideTime
            cp.post(largerOrEqual(time[pickup],minus(time[drop],maxRideTime))); //max time
            //The vehicle must arrive at the pickup node before the drop node
            cp.post(lessOrEqual(time[pickup], time[drop])); //first visit the pick up and then the drop
            // Calculate the mandatory time at the pickup node that still allows to go to the drop and then to the end depot
            //time[pickup]<=time[drop]-distanceMatrix[pickup][drop]
            cp.post(lessOrEqual(time[pickup],minus(time[drop],distanceMatrix[pickup][drop])));


            //Update distance and time DROP
            cp.post(new Element1D(distanceMatrix[drop], succ[drop], distSucc[drop]));
            cp.post(new Element1DVar(time, succ[drop], sum(time[drop], distSucc[drop])));
            //Update distance from predecessor DROP
            //AUmenta il tempo di esecuzione cp.post(new Element1DVar(time,pred[drop],sum(time[drop],mul(distPred[drop],-1))));

            //Update distance from predecessor DROP
            cp.post(new Element1D(distanceMatrix[drop],pred[drop],distPred[drop]));

            cp.post(lessOrEqual(time[drop], maxRouteDuration));
            cp.post(lessOrEqual(time[drop], dropRideStops.get(task_id).window_end));
            cp.post(lessOrEqual(time[drop], plus(time[pickup], maxRideTime))); //max time
            cp.post(largerOrEqual(time[drop], time[pickup])); //first vist the pick up and the drop
            //time[drop]>=time[pickup]+distanceMatrix[pickup][drop]
            cp.post(largerOrEqual(time[drop],plus(time[pickup],distanceMatrix[pickup][drop])));




            //Manage people
            //People on the pred of the pickup are equal to people on pickup-1
            cp.post(new Element1DVar(peopleOn,pred[pickup],minus(peopleOn[pickup],1)));


            //People on the pred of the drop are equal to people on drop+1
            cp.post(new Element1DVar(peopleOn,pred[drop],plus(peopleOn[drop],1)));

            //Capacity
            cp.post(largerOrEqual(peopleOn[pickup], 1)); //because we took a person
            cp.post(largerOrEqual(peopleOn[drop], 0)); //because we drop a person

            //Manage visitedByVehicle
            cp.post(new Element1DVar(visitedByVehicle, succ[pickup], visitedByVehicle[pickup]));
            cp.post(new Element1DVar(visitedByVehicle, succ[drop], visitedByVehicle[drop]));
            //cp.post(new Element1DVar(visitedByVehicle, pred[pickup], visitedByVehicle[pickup]));
            //cp.post(new Element1DVar(visitedByVehicle, pred[drop], visitedByVehicle[drop]));
            cp.post(new Element1DVar(visitedByVehicle, index[pickup], visitedByVehicle[drop]));
            //cp.post(new Element1DVar(visitedByVehicle, index[drop], visitedByVehicle[pickup]));

            //Manage managedBy
            cp.post(new Element1DVar(managedBy, minus(index[pickup], nVehicles), visitedByVehicle[pickup]));
            //The vehicle that manage the pickup must be the same that manage the drop
            cp.post(new Element1DVar(visitedByVehicle,index[drop], managedBy[task_id]));


            //Constrain to shrik the space
            cp.post(notEqual(pred[pickup], drop));
            cp.post(notEqual(succ[drop], pickup));


            for (int endDepot = first_end_depot; endDepot < n; endDepot++) {
                int startDepot = i - nVehicles - (number_of_tasks * 2);
                cp.post(notEqual(succ[pickup], endDepot));
                cp.post(notEqual(pred[pickup], endDepot));
                cp.post(notEqual(pred[drop], endDepot));
                cp.post(notEqual(pred[drop], startDepot));
            }
        }

        totalDist = sum(distSucc);
        obj_function=cp.minimize(totalDist);

    }

    private IntVar selectVariable(AtomicInteger selected){
        //Select First Unfixed Variable that have a pred fixed
        //Possible Vehicle that can vist
        //Check if the pred of the end depot is fixed
        int[] notEnded= new int[nVehicles];
        for (int i = 0; i < nVehicles; i++) {
            if(!pred[first_end_depot+i].isFixed()){
                notEnded[i]=1;
            }
        }

        //Now Select the first node that have a pred fixed and not a succ fixed but it's different from the lastVehicle
        //if the vehicle not arrived at the end depot is more than 1
        selected.getAndSet(-1);
        IntVar xs=null;
        for (int i = 0; i < n; i++) {
            if(!succ[i].isFixed() && pred[i].isFixed() && (selected.get()==-1 || succ[i].size()< xs.size() )){
                selected.set(i);
                xs=succ[i];
            }
        }

        if(xs==null) { //maybe the last vehicle is one so try again
            selected.getAndSet(-1);
            xs=null;
            for (int i = 0; i < n; i++) {
                if(!succ[i].isFixed() && pred[i].isFixed() && (selected.get()==-1 || succ[i].size()< xs.size() )){
                    selected.set(i);
                    xs=succ[i];
                }
            }
        }
        //if now is null so all the variable are fixed
        return xs;
    }


    public List<DialARideSolution> getSolution(int number_of_soultion){

        //Compute the first solution
        final int totalSolution = number_of_soultion;
        List<DialARideSolution> allSolutions = new ArrayList<>();

        AtomicInteger lastVehicle= new AtomicInteger();


        DFSearch dfs= makeDfs(cp, () -> {


            AtomicInteger sel=new AtomicInteger(-1);
            IntVar xs=selectVariable(sel);
            int selected=sel.get();

            if(xs==null) return EMPTY;

            //update lastVehicle
            //lastVehicle.set(visitedByVehicle[selected].max());

            // Create a list of all possible successors with their distances
            int[] nearestNodes = new int[xs.size()];
            xs.fillArray(nearestNodes);




            int curr_position= selected;
            List<Integer> nearestNodes_filtered = Arrays.stream(nearestNodes)
                    .filter(successor -> isWorth(curr_position,successor))
                    .boxed().collect(Collectors.toList());



            int mostUrgentNode = -1;
            int mostNearestNode = -1;
            double mostUrgentCost = Double.POSITIVE_INFINITY;
            double mostNearestCost = Double.POSITIVE_INFINITY;

            for (int node : nearestNodes_filtered) {
                // Calcola il costo basato sulla finestra temporale
                int windowDiff = time[node].max()-time[selected].min();
                // Calcola il costo basato sulla distanza
                int distanceCost = distanceMatrix[selected][node];
                //if(windowDiff-distanceCost==0) {mostUrgentNode=node; break;}
                // Calcola il costo totale come la somma dei costi basati sulla finestra temporale e sulla distanza
                double cost_time = getTimeWeight() * windowDiff + getDistanceWeight() * distanceCost;

                if (isAPickup(node)) {
                    cost_time = getTimeWeight() * windowDiff + getDistanceWeight() * distanceCost;
                }
                if (isADrop(node)){
                    cost_time = cost_time * dropWeight();
                }


                if (distanceCost < mostNearestCost) {
                    mostNearestCost = distanceCost;
                    mostNearestNode = node;
                }

                if (cost_time < mostUrgentCost) {
                    mostUrgentCost = cost_time;
                    mostUrgentNode = node;
                }
            }

            if (mostUrgentNode == -1) throw new InconsistencyException();
            int finalSelected = selected;
            int finalMostNearestNode = mostNearestNode;


            // Se siamo in un'iterazione avanzata e ci sono due nodi interessanti, esplorali entrambi
            if (lns_started.get() >= 1 && mostUrgentNode != mostNearestNode) {
                int timeAtCurr = time[selected].min();
                int upperLimit = time[mostUrgentNode].max();
                int timeAtNearest = timeAtCurr + distanceMatrix[selected][mostNearestNode];
                int timeAtUrgent = timeAtNearest + distanceMatrix[mostNearestNode][mostUrgentNode];
                if (timeAtUrgent <= upperLimit) {

                    return branch(
                            () -> cp.post(equal(succ[finalSelected], finalMostNearestNode)),
                            () -> cp.post(notEqual(succ[finalSelected], finalMostNearestNode))
                    );
                }
            }


            int finalMostUrgentNode = mostUrgentNode;

            return branch(() -> {
                        try {
                            cp.post(equal(succ[finalSelected], finalMostUrgentNode));
                        }catch (InconsistencyException e){
                            //System.out.println("Da "+finalSelected+"Sono tornato indetro da "+ best);

                            throw e;
                        }
                    },
                    () -> {try{
                        cp.post(notEqual(succ[finalSelected],finalMostUrgentNode));
                    }catch (InconsistencyException e){

                        throw e;
                    }
                    });
        });

        //TODO 2.7 ACTION ON SOLUTION
        final int[] bestPath = new int[n];
        final int[] bestRideID = new int[n];
        AtomicInteger curr_solution= new AtomicInteger();
        actionToDoOnASolution(dfs,allSolutions,bestPath,bestRideID,curr_solution);

        long sec= (long) 1e+9;
        //2258
        long maxTime = 540*sec;
        long startTime = ManagementFactory.getThreadMXBean().getCurrentThreadCpuTime();
        long maxRunTimeMS = maxTime;

        lns(dfs,bestPath,allSolutions,i-> (i - startTime > maxRunTimeMS ),startTime,maxRunTimeMS);

        //dfs.solve(statistics -> statistics.numberOfSolutions() ==564);

        return allSolutions;

    }

    private void actionToDoOnASolution(DFSearch dfs, List<DialARideSolution> allSolutions,int[] bestPath,int[] bestRideID,AtomicInteger curr_solution){

        dfs.onSolution(() -> {
            DialARideSolution curr_sol= new DialARideSolution(nVehicles,pickupRideStops,dropRideStops,depot,vehicleCapacity,maxRideTime,maxRouteDuration);
            System.out.println("solution: "+totalDist.min());
            //System.out.println("Max Routing Time: "+maxRouteDuration);
            for (int i = 0; i < n; i ++) bestPath[i] = succ[i].min();
            for (int i = 0; i < n; i ++) bestRideID[i] = visitedByVehicle[i].min();


            final int idx_sol= curr_solution.get();
            //System.out.println("I pickup vanno da "+nVehicles+" a "+(nVehicles+pickupRideStops.size()));
            //System.out.println("I drop vanno da "+(nVehicles+pickupRideStops.size())+" a "+(nVehicles+pickupRideStops.size()+dropRideStops.size()));
            for (int i = 0; i < nVehicles; i++) {
                int curr_node = i;
                while (curr_node < nVehicles + pickupRideStops.size() + dropRideStops.size()) {
                    int succ_node=bestPath[curr_node];
                    boolean isPickup = succ_node>=nVehicles && succ_node<nVehicles+pickupRideStops.size();
                    if(succ_node>=nVehicles+pickupRideStops.size()+dropRideStops.size()){
                        //The veichle is back to the depot
                        curr_node = succ_node;
                        break;
                    }
                    if(isPickup) {
                        curr_sol.addStop(bestRideID[curr_node],succ_node-nVehicles,isPickup);
                    }
                    else {
                        curr_sol.addStop(bestRideID[curr_node],succ_node-pickupRideStops.size()-nVehicles,isPickup);
                    }
                    curr_node = succ_node;
                }
            }
            curr_solution.getAndIncrement();
            allSolutions.add(curr_sol);

        });

    }

    private DFSearch changeSearchStrategy(){
        //Compute the first solution

        DFSearch dfs= makeDfs(cp, () -> {
            System.out.println("Ho cambiato strategia");

            //Select First Unfixed Variable that have a pred fixed
            int selected = -1;
            IntVar xs=null;
            for (int i = 0; i < n; i++) {
                if(!succ[i].isFixed() && pred[i].isFixed() && (selected==-1 || succ[i].size()<xs.size())){
                    selected=i;
                    xs=succ[i];
                }
            }
            if(xs==null) return EMPTY;


            // Get the index of the selected node
            //System.out.println(selected);



            // Create a list of all possible successors with their distances
            int[] nearestNodes = new int[xs.size()];
            xs.fillArray(nearestNodes);

            int curr_position= selected;
            List<Integer> nearestNodes_filtered = Arrays.stream(nearestNodes)
                    .filter(successor -> isWorth(curr_position,successor))
                    .boxed().collect(Collectors.toList());

            double mostUrgent = Integer.MAX_VALUE;
            double mostNearest = Integer.MAX_VALUE;
            int mostUrgentNode=-1;
            int mostNearestNode=-1;


            // Trova il nodo con il costo totale più basso come il nodo successivo
            for (int node : nearestNodes_filtered) {
                // Calcola il costo basato sulla finestra temporale
                int windowDiff = time[node].max()-time[selected].min();
                // Calcola il costo basato sulla distanza
                int distanceCost = distanceMatrix[selected][node];
                //if(windowDiff-distanceCost==0) {mostUrgentNode=node; break;}
                // Calcola il costo totale come la somma dei costi basati sulla finestra temporale e sulla distanza
                double cost_time=(windowDiff)*(distanceCost);

                // Se il nodo è un nodo di destinazione, annulla il costo associato alla finestra temporale
                if (isAPickup(node)) {
                    cost_time = windowDiff;
                }

                if (isADrop(node)) {
                    cost_time = ((windowDiff) + (distanceCost * 0.3)) * 0.8; // Only consider the cost based on the distance
                }

                if (distanceCost < mostNearest) {
                    mostNearest = distanceCost;
                    mostNearestNode = node;
                }

                if (cost_time < mostUrgent) {
                    mostUrgent = cost_time;
                    mostUrgentNode = node;
                }
            }

            if(mostUrgentNode==-1){
                throw new InconsistencyException();
            }

            int finalSelected = selected;
            int best= mostUrgentNode;
            int best_2=mostNearestNode;

            if(best!=best_2){
                return branch(
                        () -> cp.post(equal(succ[finalSelected], best_2)),
                        () -> cp.post(notEqual(succ[finalSelected], best_2))
                );
            }

            //System.out.println("Sono andato al nearest");
            return branch(() -> {
                        try {
                            cp.post(equal(succ[finalSelected], best));
                        }catch (InconsistencyException e){
                            throw e;
                        }
                    },
                    () -> {try{
                        cp.post(notEqual(succ[finalSelected],best));
                    }catch (InconsistencyException e){
                        throw e;
                    }
                    });
        });

        return dfs;

    }


    private void lns(DFSearch dfs, int[] bestPath, List<DialARideSolution> allSolutions, Predicate<Long> stopLNS,long starTime, long maxRunTimeMS){

        //Find a first solution
        dfs.optimize(obj_function,statistics -> statistics.numberOfSolutions() ==1);
        //ok founded a first solution
        lns_started.getAndIncrement();//set to one from 0;
        //dfs = changeSearchStrategy();

        Random rand = new Random(0);

        AtomicInteger failureLimit = new AtomicInteger(1000);
        AtomicInteger percentage = new AtomicInteger(70);//2313 2320 23 21 20169

        AtomicReference<List<Integer>> nodesToUnfix_at_last_iteration = new AtomicReference<>();
        AtomicInteger maxNodes= new AtomicInteger(3);
        AtomicInteger number_of_random_fix= new AtomicInteger(0);
        AtomicReference<List<Integer>> nodesFromNoStart = new AtomicReference<>(new ArrayList<>());
        AtomicInteger curr_run= new AtomicInteger(0);


        while(!stopLNS.test(ManagementFactory.getThreadMXBean().getCurrentThreadCpuTime())){



            dfs.optimizeSubjectTo(obj_function,
                    statistics -> statistics.numberOfFailures()>= failureLimit.get() || stopLNS.test(ManagementFactory.getThreadMXBean().getCurrentThreadCpuTime()),
                    ()-> {

                        lns_started.set(3);
                        curr_run.getAndIncrement();
                        //System.out.println("Random Path");
                        for (int j = 0; j < n; j++) {
                            if (rand.nextInt(100) < percentage.get() ) {
                                // after the solveSubjectTo those constraints are removed
                                if(bestPath[j]>=first_end_depot) continue; //for all the vehicle dont set the end

                                cp.post(equal(succ[j], bestPath[j]));
                            }
                        }

                        //System.out.println("ciao"+curr_run.get());


                    }

                    );
        }
    }

    private List<Integer> nodesToUnfix(int[] startIndices,int[] bestPath,int maxNodesInPath){
        //Nodes to unfix are from startIndex to endIndex
        //insert in a list the nodes to unfix

        ArrayList<Integer> nodesToUnfix = new ArrayList<>();
        for(int start_idx=0;start_idx<startIndices.length;start_idx++){
            int curr_node=startIndices[start_idx];
            int n_of_visited = 0;
            while (curr_node < nVehicles + number_of_tasks * 2 && n_of_visited < maxNodesInPath) {
                nodesToUnfix.add(curr_node);
                curr_node = bestPath[curr_node];
                n_of_visited++;
            }

        }
        return nodesToUnfix;
    }


    private void takeLongestPath(int[] maxLengths,int[] startIndices,int[] bestPath,int maxNodesInPath){

        for (int vehicle = 0; vehicle < nVehicles; vehicle++) {
            // Reset the longest path for the current vehicle
            maxLengths[vehicle] = 0;
            startIndices[vehicle] = 0;

            List<Integer> current_best_path= new ArrayList<>();
            //aggiugni tutti i nodi nel path
            int current = vehicle;
            while (current < nVehicles + pickupRideStops.size() + dropRideStops.size()) {
                current_best_path.add(current);
                current = bestPath[current];
            }
            //iterate over all the start nodes
            for(Integer curr_start:current_best_path){
                int curr_node=curr_start;
                int current_length=0;
                int visited=0;
                while(curr_node<nVehicles+pickupRideStops.size()+dropRideStops.size() && visited<maxNodesInPath){
                    current_length+=distanceMatrix[curr_node][bestPath[curr_node]];
                    curr_node=bestPath[curr_node];
                    visited++;
                }
                if(current_length>maxLengths[vehicle]){
                    maxLengths[vehicle]=current_length;
                    startIndices[vehicle]=curr_start;
                }

            }
        }



    }

    private boolean isWorth(int curr_position,int successor){

        int number_of_task=pickupRideStops.size();

        if (isADepot(successor)){
            //return true;
            return evaluateDepotNode(curr_position,successor);
        }

        else if(isADrop(successor)){
            //return true;
            return evaluateDropNode(curr_position,successor);
        }

        //it's a pickup node
        else if (isAPickup(successor)){
            //return true;
            return evaluatePickUpNode(curr_position,successor);
        }
        return true;

    }


    private boolean isADepot(int node){
        return node<nVehicles || node>=first_end_depot;
    }

    private boolean isADrop(int node){
        return node>=nVehicles+number_of_tasks && node<first_end_depot;
    }

    private boolean isAPickup(int node){
        return node>=nVehicles && node<nVehicles+number_of_tasks;
    }

    private boolean evaluateDepotNode(int curr_position, int successor){



        if(peopleOn[curr_position].max()!=0){ //you have person on the veichle
            return false;
        }

        //ok i have 0 person on the veichle and i'm at drop
        //i can go to a pickup if exist or to the end depot
        //if i go to a pickup i need to check if i can reach the drop node and then also the final depot.
        int currTime_tmp = time[curr_position].min();
        int upperBoundPickup= n-nVehicles-number_of_tasks;
        for (int i = nVehicles; i < upperBoundPickup; i++) {
            int task_id=i-nVehicles;
            if(!managedBy[task_id].isFixed()){ //not anyone visited the node i yet
                int task = i-nVehicles;
                int pickupNode = i;
                int dropNode = i+pickupRideStops.size();
                int window_end_pickup = time[pickupNode].max();
                int window_end_drop = time[dropNode].max();

                currTime_tmp+=distanceMatrix[curr_position][pickupNode];
                if(currTime_tmp>window_end_pickup){
                    //ok i cant do this task, try the next
                    continue;
                }
                currTime_tmp+=distanceMatrix[pickupNode][dropNode];
                if(currTime_tmp>window_end_drop){
                    //ok i cant do this task, try the next
                    continue;
                }
                currTime_tmp+=distanceMatrix[dropNode][successor];
                if(currTime_tmp>maxRouteDuration){
                    //ok i cant do this task, try the next

                    continue;
                }
                //ok it's not worth to go to the depot beacuse exist a path that i can do
                return false;
            }
        }

        //i cant do any task, go to the depot


        return true;
    }

    private boolean evaluateDropNode(int curr_position,int successor){
        //The nearest node is a drop so evaluate if it's worth going to this node
        //if the veichle is almost empty then it's not worth going to this node
        //eh ma aspetta e se mi sta per scadere?
        /*
        if(peopleOn[curr_position].max()==1 && !isAPickup(curr_position,nVehicles,pickupRideStops.size())){
            return false;
        }
         */
        //if the drop node it's not managed by the veichle that visit the pickup node then it's not worth going to this node

        int pickupNode=successor-pickupRideStops.size();
        //this thing doesnt work
        /*
        if(!pred[pickupNode].isFixed()){
            //!pred[pickupNode].isFixed() if true then the pickup node is not yet visited so it's not my task
            //VisitedByVehicle[pickupNode].min()!=VisitedByVehicle[curr_position].min() if true then the pickup node is not managed by my veichle
            return false;
        }

         */

        if(!managedBy[pickupNode-nVehicles].isFixed() || managedBy[pickupNode-nVehicles].max()!=visitedByVehicle[curr_position].max()){
            return false;
        }


        //if the veichle can't reach the node before the window end
        if(time[curr_position].min()+distanceMatrix[curr_position][successor]>time[successor].max()){
            throw new InconsistencyException(); //PATH IMPOSSIBILE DA RISOLVERE
            //return false;
        }




        return true;
    }

    private boolean evaluatePickUpNode(int curr_position, int successor){
        //1. If the veichle is full then it's not worth going to the pickup node
        //2. If the veichle can't reach the pickup node before the window end then it's not worth going to the pickup node
        //3. If the veichle can't reach the drop node of each task that the veichle has to do plus this task then it's not worth going to the pickup node

        //The nearest node is a pickup so evaluate if it's worth going to this node
        //if our veichle capacity is full then it's not worth going to this node
        //peopleOn[curr_node+1] because the person is not yet on the veichle

        int task_id=successor-nVehicles;



        //Take all the task that the vehicle has to do
        int vehicle_id = visitedByVehicle[curr_position].min();
        List<Integer> taskManagedByCurrentVehicle = new ArrayList<>();
        for (int i = 0; i < managedBy.length; i++) {
            int pickupNode = i+nVehicles;
            if(managedBy[i].isFixed() && visitedByVehicle[pickupNode].max()==vehicle_id){
                //ok it's a my task, but i already did it?
                int dropNode = pickupNode+pickupRideStops.size();
                if(!pred[dropNode].isFixed()){
                    //the task is not already done
                    taskManagedByCurrentVehicle.add(i);
                }
            }
        }

        //Ok add the task associated to the succesor node
        if(taskManagedByCurrentVehicle.isEmpty()){//ok i don't have any task to do
            //but i can reach the drop node of the new task?
            int start_time = time[curr_position].min()+distanceMatrix[curr_position][successor];
            int dropNode = successor+pickupRideStops.size();
            if(start_time>time[successor].max()){
                return false;
            }
            start_time+=distanceMatrix[successor][dropNode];
            if(start_time>time[dropNode].max()){
                return false;
            }
            //ok i can reach the drop node in time, but i can reach the depot?
            start_time+=distanceMatrix[dropNode][distanceMatrix.length-1];
            if(start_time>maxRouteDuration){
                return false;
            }
            //ok i can go to the nearest node without a lot of problem
            return true;
        }
        //Ok now if from current_time the total_time to go to each node is under the maxRouteDuration
        //then maybe it's worth going to the nearest node


        //ok now from the new successor node i need to check if the veichle can reach the drop node of each task
        //that the veichle has to do in window_end order

        taskManagedByCurrentVehicle.sort
                (Comparator.comparingInt(task ->
                        time[task+nVehicles+number_of_tasks].max()));

        int mostUrgentTask = taskManagedByCurrentVehicle.get(0);
        int mostUrgentPickup = mostUrgentTask+nVehicles;
        int mostUrgentDrop = mostUrgentPickup+pickupRideStops.size();
        int start_time_most_urgent = time[mostUrgentPickup].min();

        int currTime_tmp = time[curr_position].min()+distanceMatrix[curr_position][successor];
        int currNode_tmp = successor;
        currTime_tmp+=distanceMatrix[currNode_tmp][mostUrgentDrop];
        if(currTime_tmp>time[mostUrgentDrop].max()){
            return false;
        }
        if(currTime_tmp>maxRouteDuration){
            return false;
        }
        if(currTime_tmp-start_time_most_urgent>maxRideTime){
            return false;
        }
        //Ok we can go to the nearest node without a lot of problem maybe
        return true;


    }

    private static void computeDistanceMatrix(int[][] distanceMatrix, int nVehicles, int number_of_tasks,
                                              ArrayList<RideStop> pickupAndDropRideStops, RideStop depot){
        int first_end_depot=nVehicles+(number_of_tasks*2);
        for (int i = 0 ; i < distanceMatrix.length ; ++i) {
            for (int j = 0 ; j < distanceMatrix.length; ++j) {

                if(i<nVehicles && j<nVehicles){
                    //i and j are depots
                    distanceMatrix[i][j] = 0;
                }
                else if(i<nVehicles && !(j>=first_end_depot)){
                    //only i is a depot
                    distanceMatrix[i][j] = distance(depot, pickupAndDropRideStops.get(j-nVehicles));
                }
                else if(j<nVehicles && !(i>first_end_depot)){
                    //only j is a depot
                    distanceMatrix[i][j] = distance(pickupAndDropRideStops.get(i-nVehicles), depot);
                }
                else if (i < first_end_depot && j < first_end_depot){
                    //i and j are not depots
                    distanceMatrix[i][j] = distance(pickupAndDropRideStops.get(i-nVehicles), pickupAndDropRideStops.get(j-nVehicles));
                }
                else if(i>=first_end_depot && j>=first_end_depot){
                    //i and j are end depots
                    distanceMatrix[i][j]=0;
                }
                else if(i>=first_end_depot && j<nVehicles){
                    //i is a end depot and j is a start depot
                    distanceMatrix[i][j] =0;
                }
                else if(j>=first_end_depot && i<nVehicles){
                    //j is a end depot and i is a start depot
                    distanceMatrix[i][j] = 0;
                }
                else if(i>=first_end_depot){
                    //i is a end depot and j is a place
                    distanceMatrix[i][j] = distance(depot, pickupAndDropRideStops.get(j-nVehicles));
                }
                else if(j>=first_end_depot){
                    //j is a end depot and i is a place
                    distanceMatrix[i][j] = distance(pickupAndDropRideStops.get(i-nVehicles), depot);
                }
            }
        }

    }


    private static void buildPickUpAndDrop(ArrayList<RideStop> pickupAndDropRideStops, ArrayList<RideStop> pickupRideStops, ArrayList<RideStop> dropRideStops, RideStop depot, int number_of_end_depots, int maxRouteDuration){
        pickupAndDropRideStops.addAll(pickupRideStops);
        pickupAndDropRideStops.addAll(dropRideStops);
        for (int i = 0; i < number_of_end_depots; i++) {
            RideStop endDepot = new RideStop();
            endDepot.type=0;
            endDepot.pos_x=depot.pos_x;
            endDepot.pos_y=depot.pos_y;
            endDepot.window_end=maxRouteDuration;
            pickupAndDropRideStops.add(endDepot);
        }
    }

    public static DialARideSolution solve(int nVehicles, int maxRouteDuration, int vehicleCapacity,
                                          int maxRideTime, ArrayList<RideStop> pickupRideStops, ArrayList<RideStop> dropRideStops,
                                          RideStop depot) {

        //Create the model
        DialARide dialARide = new DialARide(nVehicles, maxRouteDuration, vehicleCapacity, maxRideTime, pickupRideStops, dropRideStops, depot);
        dialARide.buildModel();
        List<DialARideSolution> sol=dialARide.getSolution(1);
        if(sol.isEmpty()){
            return null;
        }
        int best_solution=Integer.MAX_VALUE;
        int best_solution_idx=-1;
        int index=0;
        for (DialARideSolution dialARideSolution : sol) {
            int curr=dialARideSolution.compute();
            if(curr<best_solution){
                best_solution=curr;
                best_solution_idx=index;
            }
            index++;
        }
        return sol.get(best_solution_idx);


    }


    public static List<DialARideSolution> findAll(int nVehicles, int maxRouteDuration, int vehicleCapacity,
                                                  int maxRideTime, ArrayList<RideStop> pickupRideStops, ArrayList<RideStop> dropRideStops,
                                                  RideStop depot) {
        DialARide dialARide = new DialARide(nVehicles, maxRouteDuration, vehicleCapacity, maxRideTime, pickupRideStops, dropRideStops, depot);
        dialARide.buildModel();


        return dialARide.getSolution(1000);
    }

    /**
     * Returns the distance between two ride stops
     */
    public static int distance(RideStop a, RideStop b) {
        return (int) (Math.sqrt((a.pos_x - b.pos_x) * (a.pos_x - b.pos_x) + (a.pos_y - b.pos_y) * (a.pos_y - b.pos_y)) * 100);
    }

    /**
     * A solution. To create one, first do new DialARideSolution, then
     * add, for each vehicle, in order, the pickup/drops with addStop(vehicleIdx, rideIdx, isPickup), where
     * vehicleIdx is an integer beginning at 0 and ending at nVehicles - 1, rideIdx is the id of the ride you (partly)
     * fullfill with this stop (from 0 to pickupRideStops.size()-1) and isPickup a boolean indicate if you are beginning
     * or ending the ride. Do not add the last stop to the depot, it is implicit.
     * <p>
     * You can check the validity of your solution with compute(), which returns the total distance, and raises an
     * exception if something is invalid.
     * <p>
     * DO NOT MODIFY THIS CLASS.
     */
    public static class DialARideSolution {
        public ArrayList<Integer>[] stops;
        public ArrayList<RideStop> pickupRideStops;
        public ArrayList<RideStop> dropRideStops;
        public RideStop depot;
        public int capacity;
        public int maxRideTime;
        public int maxRouteDuration;

        public String toString() {
            StringBuilder b = new StringBuilder();
            b.append("Length: ");
            b.append(compute());
            b.append("\n");
            for (int i = 0; i < stops.length; i++) {
                b.append("- ");
                for (int s : stops[i]) {
                    if (s >= pickupRideStops.size()) {
                        b.append(s - pickupRideStops.size());
                        b.append("d, ");
                    } else {
                        b.append(s);
                        b.append("p, ");
                    }
                }
                b.append("\n");
            }
            return b.toString();
        }

        public DialARideSolution(int nVehicles, ArrayList<RideStop> pickupRideStops, ArrayList<RideStop> dropRideStops,
                                 RideStop depot, int vehicleCapacity, int maxRideTime, int maxRouteDuration) {
            stops = new ArrayList[nVehicles];
            for (int i = 0; i < nVehicles; i++)
                stops[i] = new ArrayList<>();

            this.pickupRideStops = pickupRideStops;
            this.dropRideStops = dropRideStops;
            this.depot = depot;
            this.capacity = vehicleCapacity;
            this.maxRideTime = maxRideTime;
            this.maxRouteDuration = maxRouteDuration;
        }

        /**
         * Add a stop on the path of a vehicle
         * No need to add the last stop to the depot, it is implicit
         *
         * @param vehicleId id of the vehicle where the stop occurs
         * @param rideId    id of the ride related to the stop
         * @param isPickup  true if the point is the pickup of the ride, false if it is the drop
         */
        public void addStop(int vehicleId, int rideId, boolean isPickup) {
            stops[vehicleId].add(rideId + (isPickup ? 0 : pickupRideStops.size()));
        }

        public int compute() {
            int totalLength = 0;
            HashSet<Integer> seenRides = new HashSet<>();

            for (int vehicleId = 0; vehicleId < stops.length; vehicleId++) {
                HashMap<Integer, Integer> inside = new HashMap<>();
                RideStop current = depot;
                int currentLength = 0;
                for (int next : stops[vehicleId]) {
                    RideStop nextStop;
                    if (next < pickupRideStops.size())
                        nextStop = pickupRideStops.get(next);
                    else
                        nextStop = dropRideStops.get(next - pickupRideStops.size());

                    currentLength += distance(current, nextStop);

                    if (next < pickupRideStops.size()) {
                        if (seenRides.contains(next))
                            throw new RuntimeException("Ride stop visited twice");
                        seenRides.add(next);
                        inside.put(next, currentLength);
                    } else {
                        if (!inside.containsKey(next - pickupRideStops.size()))
                            throw new RuntimeException("Drop before pickup");
                        if (inside.get(next - pickupRideStops.size()) + maxRideTime < currentLength)
                            throw new RuntimeException("Ride time too long");
                        inside.remove(next - pickupRideStops.size());
                    }

                    if (currentLength > nextStop.window_end)
                        throw new RuntimeException("Ride stop visited too late");
                    if (inside.size() > capacity)
                        throw new RuntimeException("Above maximum capacity");

                    current = nextStop;
                }

                currentLength += distance(current, depot);

                if (inside.size() > 0)
                    throw new RuntimeException("Passenger never dropped");
                if (currentLength > maxRouteDuration)
                    throw new RuntimeException("Route too long");

                totalLength += currentLength;
            }

            if (seenRides.size() != pickupRideStops.size())
                throw new RuntimeException("Some rides never fulfilled");

            return totalLength;
        }
    }

    static class RideStop {
        public float pos_x;
        public float pos_y;
        public int type; //0 == depot, 1 == pickup, -1 == drop
        public int window_end;
    }

    public static RideStop readRide(InputReader reader) {
        try {
            RideStop r = new RideStop();
            reader.getInt(); //ignored
            r.pos_x = Float.parseFloat(reader.getString());
            r.pos_y = Float.parseFloat(reader.getString());
            reader.getInt(); //ignored
            r.type = reader.getInt();
            reader.getInt(); //ignored
            r.window_end = reader.getInt() * 100;
            return r;
        } catch (Exception e) {
            return null;
        }
    }

    public static void main(String[] args) {
        // Reading the data

        //TODO change file to test the various instances.
        InputReader reader = new InputReader(args[0]);

        int nVehicles = reader.getInt();
        reader.getInt(); //ignore
        int maxRouteDuration = reader.getInt() * 100;
        int vehicleCapacity = reader.getInt();
        int maxRideTime = reader.getInt() * 100;

        RideStop depot = null;
        ArrayList<RideStop> pickupRideStops = new ArrayList<>();
        ArrayList<RideStop> dropRideStops = new ArrayList<>();
        boolean lastWasNotDrop = true;
        while (true) {
            RideStop r = readRide(reader);
            if (r == null)
                break;
            if (r.type == 0) {
                assert depot == null;
                depot = r;
            } else if (r.type == 1) {
                assert lastWasNotDrop;
                pickupRideStops.add(r);
            } else { //r.type == -1
                lastWasNotDrop = false;
                dropRideStops.add(r);
            }
        }
        assert depot != null;
        assert pickupRideStops.size() == dropRideStops.size();

        DialARideSolution sol = solve(nVehicles, maxRouteDuration, vehicleCapacity, maxRideTime, pickupRideStops, dropRideStops, depot);
        System.out.println(sol);
    }
}
