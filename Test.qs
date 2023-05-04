namespace Quantum.Week1_StandaloneProjectTest {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Diagnostics;

    open Quantum.Week1_StandaloneProject;

    @Test("QuantumSimulator")
    operation TestSumOptions(): Unit {
        let constraint1 = SEC([2,3,4], 3);
        let constraint2 = SEC([0,1], 1);
        let expectedOptions1 = [[2,0,1], [0,2,1], [0,1,2], [2,1,0], [1,2,0], [1,0,2], [1,0,2], [0,1,2], [0,2,1],
        [1,2,0], [2,1,0], [2,0,1], [0,1,2], [1,0,2], [1,2,0], [0,2,1], [2,0,1], [2,1,0]];
        let expectedOptions2 = [[0, 1], [1, 0]];
        let sumOptions1 = SumOptions(constraint1);
        let sumOptions2 = SumOptions(constraint2);
        Message($"Sum options for constraint {constraint1} are {sumOptions1}");
        Message($"Sum options for constraint {constraint2} are {sumOptions2}");
        for i in 0 .. Length(expectedOptions1) - 1 {
            AllEqualityFactI(sumOptions1[i], expectedOptions1[i], $"Sum option is wrong: actual {sumOptions1[i]}, expected {expectedOptions1[i]}");
        }
        for i in 0 .. Length(expectedOptions2) - 1 {
            AllEqualityFactI(sumOptions2[i], expectedOptions2[i], $"Sum option is wrong: actual {sumOptions2[i]}, expected {expectedOptions2[i]}");
        }
    }

    @Test("QuantumSimulator")
    operation TestFindSumConstraints(): Unit {
        let nVariables = 7;
        let sumEqualityConstraints = [
            SEC([0,1], 3),
            SEC([0,2], 5),
            SEC([1,3,5], 3),
            SEC([2,3,4], 5),
            SEC([4,6], 1),
            SEC([5,6], 1)
        ];
        let sumConstraints = FindSumConstraints(sumEqualityConstraints, nVariables);
        let expected = [(0, 0),(0, 1),(1, 3),(2, 0),(2, 1),(3, 1),(3, 3),(4, 1),(4, 2),(4, 3),(5, 2),(5, 3),(6, 2),(6, 3)];
        for i in 0 .. Length(expected) - 1 {
            let (expI, expJ) = expected[i];
            let (sumConI, sumConJ) = sumConstraints[i];
            EqualityFactI(sumConI, expI, $"Sum constraint {i} has wrong first index");
            EqualityFactI(sumConJ, expJ, $"Sum constraint {i} has wrong first index");
        }
    }

    @Test("QuantumSimulator")
    operation TestApplyVariableValuesOracles(): Unit {
        let nVariables = 7;
        let valueQubits = 2;
        let inequalityConstraints = [(0,1), (0,2), (1,3), (1,5), (2,3), (2,4), (3,4), (3,5), (4,6), (5,6)];
        let variableValues = [true, false, false, true, true, true, true, false, false, false, false, false, false, true];
        use (valueRegister, target) = (Qubit[valueQubits*nVariables], Qubit());
        ApplyPauliFromBitString(PauliX, true, variableValues, valueRegister);
        ApplyVariableValuesOracles(nVariables, valueQubits, inequalityConstraints, valueRegister, target);
        AssertQubit(One, target);
        ResetAll(valueRegister+[target]);
    }

    @Test("QuantumSimulator")
    operation TestSolvePuzzle(): Unit {
        let size = (4, 4);
        let nVariables = 7;
        let valueQubits = 2;
        let inequalityConstraints = [(0,1), (0,2), (1,3), (1,5), (2,3), (2,4), (3,4), (3,5), (4,6), (5,6)];
        let sumEqualityConstraints = [
            SEC([0,1], 3),
            SEC([0,2], 5),
            SEC([1,3,5], 3),
            SEC([2,3,4], 5),
            SEC([4,6], 1),
            SEC([5,6], 1)
        ];
        let (isValid, result) = SolvePuzzle(nVariables, valueQubits, size, inequalityConstraints, sumEqualityConstraints);
        Fact(isValid, "Puzzle solution is not valid");
    }


    @Test("QuantumSimulator")
    operation TestIsKakuroSolutionValid(): Unit {
        let inequalityConstraints = [(0,1), (0,2), (1,3), (1,5), (2,3), (2,4), (3,4), (3,5), (4,6), (5,6)];
        let sumEqualityConstraints = [
            SEC([0,1], 3),
            SEC([0,2], 5),
            SEC([1,3,5], 3),
            SEC([2,3,4], 5),
            SEC([4,6], 1),
            SEC([5,6], 1)
        ];
        let validValues = [2,1,3,2,0,0,1];
        let invalidValues = [2,1,2,3,0,0,1];
        let isValid = IsKakuroSolutionValid(inequalityConstraints, sumEqualityConstraints, validValues);
        let notValid = IsKakuroSolutionValid(inequalityConstraints, sumEqualityConstraints, invalidValues);
        Fact(isValid, "Valid solution is showing as not valid");
        Contradiction(notValid, "Invalid solution is showing as valid");
    }
}