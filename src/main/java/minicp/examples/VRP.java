package minicp.examples;

import minicp.engine.constraints.Circuit;
import minicp.engine.constraints.Element1D;
import minicp.engine.core.IntVar;
import minicp.engine.core.Solver;
import minicp.search.SearchStatistics;
import minicp.util.exception.NotImplementedException;
import minicp.util.io.InputReader;

import static minicp.cp.BranchingScheme.*;
import static minicp.cp.Factory.*;
import static minicp.cp.Factory.notEqual;

public class VRP extends OptimizationProblem{

    public final int initalNodes;
    public final int nVehicle;
    public final int[][] initialDistanceMatrix;
    public int[][] distanceMatrix;
    public IntVar[] succ;
    public IntVar totalDist;
    public int n;
    String instance;

    public VRP(String instancePath, int nVehicle) {
        InputReader reader = new InputReader(instancePath);
        this.nVehicle = nVehicle;
        instance = reader.getFilename();
        initalNodes = reader.getInt();
        initialDistanceMatrix = reader.getMatrix(initalNodes, initalNodes);
    }


    @Override
    public void buildModel() {

        int duplicate_depot= nVehicle-1;
        n = initalNodes+duplicate_depot;


        distanceMatrix = new int[n][n];
        for (int i = 0 ; i < distanceMatrix.length ; ++i) {
            for (int j = 0 ; j < distanceMatrix.length; ++j) {

                if(i<nVehicle && j<nVehicle){
                    //i and j are depots
                    distanceMatrix[i][j] = 0;
                }
                else if(i<nVehicle){
                    //only i is a depot
                    distanceMatrix[i][j] = initialDistanceMatrix[0][j-duplicate_depot];
                }
                else if(j<nVehicle){
                    //only j is a depot
                    distanceMatrix[i][j] = initialDistanceMatrix[i-duplicate_depot][0];
                }
                else{
                    //i and j are not depots
                    distanceMatrix[i][j] = initialDistanceMatrix[i-duplicate_depot][j-duplicate_depot];
                }
            }
        }

        Solver cp = makeSolver();
        succ = makeIntVarArray(cp, n, n);
        IntVar[] distSucc = makeIntVarArray(cp, n, 1000);
        cp.post(new Circuit(succ));
        for (int i = 0; i < n; i++) {
            cp.post(new Element1D(distanceMatrix[i], succ[i], distSucc[i]));
        }
        totalDist = sum(distSucc);
        objective = cp.minimize(totalDist);

        // simple first-fail strategy. You can optionally change it, but it is not required to pass the exercise
        dfs = makeDfs(cp, () -> {
            IntVar xs = selectMin(succ,
                  xi -> xi.size() > 1,
                    IntVar::size);
            if (xs == null)
                return EMPTY;
            else {
                int v = xs.min();
                return branch(() -> xs.getSolver().post(equal(xs, v)),
                        () -> xs.getSolver().post(notEqual(xs, v)));
            }
        });
    }

    @Override
    public String toString() {
        return "VRP(" + instance + ',' + nVehicle + ')';
    }

    public static void main(String[] args) {
        // instance gr17 https://people.sc.fsu.edu/~jburkardt/datasets/tsp/gr17_d.txt
        // instance fri26 https://people.sc.fsu.edu/~jburkardt/datasets/tsp/fri26_d.txt
        // instance p01 (adapted from) https://people.sc.fsu.edu/~jburkardt/datasets/tsp/p01_d.txt
        // the other instances are located at data/tsp/ and adapted from https://lopez-ibanez.eu/tsptw-instances
        VRP vrp = new VRP("data/tsp/tsp_15.txt", 1);
        vrp.buildModel();
        SearchStatistics stats = vrp.solve(true, s -> s.numberOfSolutions() == 1);
        System.out.println(stats);
    }

}
