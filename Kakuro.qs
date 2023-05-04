namespace Quantum.Week1_StandaloneProject {

    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Logical;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Preparation;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Measurement;

    newtype SEC = (variables: Int[], sum: Int);

    // Helper function to check if a number is present in an array
    function IsNumberPresentInArray(n : Int, array : Int[]) : Bool {
        return Any(EqualI(_, n), array);
    }

    // Helper function to find the common elements in two arrays
    function FindCommonElementsInArrays(array1: Int[], array2: Int[]): Int[] {
        mutable result = [];
        for i in 0 .. Length(array1) - 1 {
            if IsNumberPresentInArray(array1[i], array2) {
                set result += [array1[i]];
            }
        }
        return result;
    }

    // Helper function to remove duplicates from an array
    function RemoveDuplicates(arr: Int[]): Int[] {
        mutable result = [];
        for i in 0 .. Length(arr) - 1 {
            if not IsNumberPresentInArray(arr[i], result) {
                set result += [arr[i]];
            }
        }
        return result;
    }

    // Helper function to get list of possible options not in limitations
    function GetLimitationConstraints(options: Int[], limitations: Int[]): Int[] {
        mutable result = [];
        for limitation in limitations {
            if not IsNumberPresentInArray(limitation, options) {
                set result += [limitation];
            }
        }
        return result;
    }

    // Gets all the possible sum options for a given constraint
    function SumOptions(constriant: SEC): Int[][] {
        mutable result = [];
        let variables = constriant::variables;
        let sumValue = constriant::sum;
        if Length(variables) == 2 {
            for i in 0 .. 3 {
                if sumValue - i < 4 and sumValue - i > -1 {
                    if i != sumValue - i {
                        set result += [[i, sumValue - i]];
                    }
                }
            }
        } elif Length(variables) == 3 {
            for i in 0 .. 3 {
                if sumValue - i < 4 and sumValue - i > -1 {
                    let options = SumOptions(SEC([0,1], i));
                    for o in options {
                        if sumValue - i != o[0] and sumValue - i != o[1] and o[0] != o[1] {
                            set result += [[sumValue-i, o[0], o[1]]];
                            set result += [[o[0], sumValue-i, o[1]]];
                            set result += [[o[0], o[1], sumValue-i]];
                        }
                    }
                }
            }
        }
        return result;
    }

    // Find the puzzle empty variables and there sums
    // Then gets the sum constraints for each empty variable
    function FindSumConstraints(sumEqualityConstraints: SEC[], nVariables: Int): (Int,Int)[] {
        mutable result = [];
        let limitations = [0, 1, 2, 3];
        for i in 0 .. nVariables - 1 {
            mutable x = 0;
            mutable options1 = [];
            mutable options2 = [];
            mutable finalOptions = [];
            for constriaint in sumEqualityConstraints {
                let variables = constriaint::variables;
                for j in 0 .. Length(variables) - 1 {
                    if variables[j] == i {
                        if x == 0 {
                            for option in SumOptions(constriaint) {
                                set options1 += [option[j]];
                            }
                        } elif x == 1 {
                            for option in SumOptions(constriaint) {
                                set options2 += [option[j]];
                            }
                            set finalOptions = RemoveDuplicates(FindCommonElementsInArrays(options1, options2));
                        }
                        set x += 1;
                    }
                }
            }
            Message($"Possible value(s) for X{i}: {finalOptions}");
            let LimitedOptions = GetLimitationConstraints(finalOptions, limitations);

            for option in LimitedOptions {
                set result += [(i, option)];
            }
        }

        Message($"Sum constraints: {result}");
        return result;
    }

    // Read value from a register
    operation MeasureValue (register: Qubit[]): Int {
        return MeasureInteger(LittleEndian(register));
    }
    
    // Read all values from a register
    operation MeasureAllValues (valueQubits: Int, register: Qubit[]): Int[] {
        let nVariables = Length(register) / valueQubits;
        let valuePartitions = Partitioned([valueQubits, size=(nVariables - 1)], register);
        return ForEach(MeasureValue, valuePartitions);
    }

    // Checks if the value of two variables are the same
    operation ApplyValueEqualityOracle(vqb0: Qubit[], vqb1: Qubit[], target: Qubit): Unit is Adj + Ctl {
        within {
            // Iterates over pair of (vqb0, vqb1)
            // Then computes XOR of bits vqb0[i] and vqb1[i] in place (storing it in vqb1[i])
            ApplyToEachCA(CNOT, Zipped(vqb0, vqb1));
        } apply {
            // If all computed XORs are 0, then the values are equal, flip the target qubit
            ControlledOnInt(0, X)(vqb1, target);
        }
    }

    // Checks if the variable values satisfy the inequality constraints
    operation ApplyVariableValuesOracles (nVariables :Int, valueQubits: Int,
        inequalityConstraints: (Int, Int)[],
        valueRegister: Qubit[], target: Qubit
    ): Unit is Adj + Ctl {
        let nInequalityConstraints = Length(inequalityConstraints);
        use inequalityConflictQubits = Qubit[nInequalityConstraints];
        within {
            for ((start, end), conflictQubit) in Zipped(inequalityConstraints, inequalityConflictQubits) {
                // if the values are the same the result will be 1, indicating a conflict
                ApplyValueEqualityOracle(
                    valueRegister[start * valueQubits .. (start + 1) * valueQubits - 1],
                    valueRegister[end * valueQubits .. (end + 1) * valueQubits - 1],
                    conflictQubit
                );
            }
        } apply {
            // If no conflicts (all qubits are in 0 state), the variable is valid
            ControlledOnInt(0, X)(inequalityConflictQubits, target);
        }
    }

    // Convert the marking oracle to a phase oracle
    operation ApplyPhaseOracle (oracle : ((Qubit[], Qubit) => Unit is Adj), register : Qubit[]): Unit is Adj {
        use target = Qubit();
        within {
            // Put the target into the |-⟩ state.
            X(target);
            H(target);
        } apply {
            // Apply the marking oracle; since the target is in the |-⟩ state,
            // flipping the target if the register satisfies the oracle condition
            // will apply a -1 factor to the state.
            oracle(register, target);
        // We put the target back into |0⟩ so we can return it.
        }
    }

    // Unitary implementing Grover's search algorithm
    operation ApplyGroversIteration(register: Qubit[],
        oracle: ((Qubit[], Qubit) => Unit is Adj),
        statePrep: (Qubit[] => Unit is Adj), iterations: Int
    ): Unit {
        let applyPhaseOracle = ApplyPhaseOracle(oracle, _);
        statePrep(register);

        for _ in 1 .. iterations {
            applyPhaseOracle(register);
            within {
                Adjoint statePrep(register);
                ApplyToEachA(X, register);
            } apply {
                Controlled Z(Most(register), Tail(register));
            }
        }
    }

    // Grover search to find variable valid values
    operation FindValuesWithGrover(nVariables: Int, valueQubits: Int, nIterations: Int,
        oracle:((Qubit[], Qubit) => Unit is Adj),
        statePrep: (Qubit[] => Unit is Adj)
    ): Int[] {
        // The value register has bits per value for each variable
        use register = Qubit[valueQubits * nVariables];
        Message($"Trying search with {nIterations} iterations...");
        if (nIterations > 75) {
            Message($"Warning: This might take a while");
        }
        ApplyGroversIteration(register, oracle, statePrep, nIterations);
        return MeasureAllValues(valueQubits, register);
    }
    
    // Show the size of the search space, i.e. the number of possible combinations
    function SearchSpaceSize(nVariables: Int, valueQubits: Int, sumConstraints: (Int, Int)[]): Int {
        mutable valueOptions = [1 <<< valueQubits, size=nVariables];
        for (cell, _) in sumConstraints {
            set valueOptions w/= cell <- valueOptions[cell] - 1;
        }
        return Fold(TimesI, 1, valueOptions);
    }

    // Estimate the number of iterations required for solution
    // Kakuro puzzles only have one solution, so we can use the formula
    function NIterations(searchSpaceSize: Int): Int {
        let angle = ArcSin(1. / Sqrt(IntAsDouble(searchSpaceSize)));
        let nIterations = Round(0.25 * PI() / angle - 0.5);
        return nIterations;
    }

    // Encodes sum constraints into amplitudes
    function AllowedAmplitudes(nVariables: Int, valueQubits: Int, sumConstraints: (Int, Int)[]) : Double[][] {
        mutable amplitudes = [[1.0, size=1 <<< valueQubits], size=nVariables];
        for (cell, value) in sumConstraints {
            set amplitudes w/= cell <- (amplitudes[cell] w/ value <- 0.0);
        }
        return amplitudes;
    }

    // Prepare an equal superposition of all basis states that satisfy the constraints
    operation PrepareSearchStatesSuperposition(nVariables: Int, valueQubits: Int,
        sumConstraints: (Int, Int)[], register : Qubit[]
    ): Unit is Adj + Ctl {
        // Split the given register into nVariables chunks of size bits per value
        let valueRegister = Chunks(valueQubits, register);
        // For each variable, create an array of possible states we're looking at
        let amplitudes = AllowedAmplitudes(nVariables, valueQubits, sumConstraints);
        // For each variable, prepare a superposition of its possible states on the chunk storing its value
        for (amps, chunk) in Zipped(amplitudes, valueRegister) {
            PrepareArbitraryStateD(amps, LittleEndian(chunk));
        }
    }

    // Checks if the value found for each empty variable is corrrect and satisfies all constraints
    function IsKakuroSolutionValid(inequalityConstraints: (Int,Int)[],
        sumEqualityConstraints: SEC[], values: Int[]
    ) : Bool {
        if (Any(GreaterThanOrEqualI(_, 4), values)) {
            return false;
        }
        if (Any(EqualI, inequalityConstraints)) { 
            return false; 
        }

        for constraint in sumEqualityConstraints {
            let variables = constraint::variables;
            let expectedSum = constraint::sum;
            mutable valuesSum = 0;
            for variable in variables {
                set valuesSum += values[variable];
            }
            if valuesSum != expectedSum {
                return false;
            }
        }
        
        return true;
    }

    operation SolvePuzzle(nVariables: Int, valueQubits: Int, size: (Int,Int), inequalityConstraints: (Int,Int)[], sumEqualityConstraints: SEC[]): (Bool, Int[]) {
        let oracle = ApplyVariableValuesOracles(nVariables, valueQubits, inequalityConstraints, _, _);
        let sumConstraints = FindSumConstraints(sumEqualityConstraints, nVariables);
        let statePrep = PrepareSearchStatesSuperposition(nVariables, valueQubits, sumConstraints, _);
        let searchSpaceSize = SearchSpaceSize(nVariables, valueQubits, sumConstraints);
        let numIterations = NIterations(searchSpaceSize);
        let (nRows, nCols) = size;

        Message($"Running Quantum test with number of variables = {nVariables}");
        Message($"   Bits per value = {valueQubits}");
        Message($"   Inequality constraints = {inequalityConstraints}");
        Message($"   Sum Equality Constraints = {sumEqualityConstraints}");
        Message($"   Estimated number iterations needed = {numIterations}");
        Message($"   Size of kakuro grid = {nRows}x{nCols}");
        Message($"   Search space size = {searchSpaceSize}");
        let values = FindValuesWithGrover(nVariables, valueQubits, numIterations, oracle, statePrep);

        Message($"Got Sudoku solution: {values}");
        if (IsKakuroSolutionValid(inequalityConstraints, sumEqualityConstraints, values)) {
           Message($"Got valid Sudoku solution: {values}");
           return (true, values);
        } else {
           Message($"Got invalid Sudoku solution: {values}");
           return (false, values);
        }
    }

    // @EntryPoint()
    operation Start(): Unit {

        Message("Solving Kakuro Puzzle using Grover's Algorithm");

        // the size of the puzzle
        let size = (4, 4);
        // let size = (3, 3);

        // number of missing boxes
        let nVariables = 7;
        // let nVariables = 4;

        // bits to represent missing value for 0 .. 3
        let valueQubits = 2;

        // array of varibles that can not be equal
        let inequalityConstraints = [(0,1), (0,2), (1,3), (1,5), (2,3), (2,4), (3,4), (3,5), (4,6), (5,6)];
        // let inequalityConstraints = [(0,1), (0,2), (1,3), (2,3)];

        // array of sum equality constraints
        let sumEqualityConstraints = [
            SEC([0,1], 3),
            SEC([0,2], 5),
            SEC([1,3,5], 3),
            SEC([2,3,4], 5),
            SEC([4,6], 1),
            SEC([5,6], 1)
        ];
        // let sumEqualityConstraints = [
        //     SEC([0,1], 4),
        //     SEC([0,2], 5),
        //     SEC([1,3], 1),
        //     SEC([2,3], 2)
        // ];

        let result = SolvePuzzle(nVariables, valueQubits, size, inequalityConstraints, sumEqualityConstraints);
        let (isValid, values) = result;
        if isValid {
            for i in 0 .. nVariables - 1 {
                Message($"X{i} = {values[i]}");
            }
        }
    }
}
 