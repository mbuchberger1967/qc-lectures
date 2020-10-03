// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT license.

namespace Quantum.Kata.GroversAlgorithm {
    
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Arrays;
    
    
    //////////////////////////////////////////////////////////////////
    // Welcome!
    //////////////////////////////////////////////////////////////////
    
    // The "Grover's Search" quantum kata is a series of exercises designed
    // to get you familiar with Grover's search algorithm.
    // It covers the following topics:
    //  - writing oracles for Grover's search,
    //  - performing steps of the algorithm, and
    //  - putting it all together: Grover's search algorithm.
    
    // Each task is wrapped in one operation preceded by the description of the task.
    // Each task (except tasks in which you have to write a test) has a unit test associated with it,
    // which initially fails. Your goal is to fill in the blank (marked with // ... comment)
    // with some Q# code to make the failing test pass.
    
    // Within each section, tasks are given in approximate order of increasing difficulty;
    // harder ones are marked with asterisks.
    
    
    //////////////////////////////////////////////////////////////////
    // Part I. Oracles for Grover's Search
    //////////////////////////////////////////////////////////////////
    
    // Task 1.1. The |11...1⟩ oracle
    // Inputs:
    //      1) N qubits in an arbitrary state |x⟩ (input/query register)
    //      2) a qubit in an arbitrary state |y⟩ (target qubit)
    // Goal: Flip the state of the target qubit (i.e., apply an X gate to it)
    //       if the query register is in the |11...1⟩ state,
    //       and leave it unchanged if the query register is in any other state.
    //       Leave the query register in the same state it started in.
    // Example:
    //       If the query register is in state |00...0⟩, leave the target qubit unchanged.
    //       If the query register is in state |10...0⟩, leave the target qubit unchanged.
    //       If the query register is in state |11...1⟩, flip the target qubit.
    //       If the query register is in state (|00...0⟩ + |11...1⟩) / sqrt(2), and the target is in state |0⟩,
    //       the joint state of the query register and the target qubit should be (|00...00⟩ + |11...11⟩) / sqrt(2).
    operation Oracle_AllOnes (queryRegister : Qubit[], target : Qubit) : Unit{
        
        body (...) {
            Controlled X(queryRegister, target);
        }
        
        adjoint self;
    }
    
    
    // Task 1.2. The |1010...⟩ oracle
    // Inputs:
    //      1) N qubits in an arbitrary state |x⟩ (input/query register)
    //      2) a qubit in an arbitrary state |y⟩ (target qubit)
    // Goal:  Flip the state of the target qubit if the query register is in the |1010...⟩ state;
    //        that is, the state with alternating 1 and 0 values, with any number of qubits in the register.
    //        Leave the state of the target qubit unchanged if the query register is in any other state.
    //        Leave the query register in the same state it started in.
    // Example:
    //        If the register is in state |0000000⟩, leave the target qubit unchanged.
    //        If the register is in state |10101⟩, flip the target qubit.
    operation Oracle_AlternatingBits (queryRegister : Qubit[], target : Qubit) : Unit {
        
        body (...) {
            // Flip all odd positions
            FlipOddPositionBits(queryRegister);
            // this creates |11..1> if it was |1010..> before
            Controlled X(queryRegister, target);
            // undo flipping
            Adjoint FlipOddPositionBits(queryRegister);
        }
        
        adjoint self;
    }
    
    operation FlipOddPositionBits(register : Qubit[]) : Unit is Adj {
        for (i in 1..2..Length(register)-1) {
            X(register[i]);
        }
    }
    
    // Task 1.3. Arbitrary bit pattern oracle
    // Inputs:
    //      1) N qubits in an arbitrary state |x⟩ (input/query register)
    //      2) a qubit in an arbitrary state |y⟩ (target qubit)
    //      3) a bit pattern of length N represented as Bool[]
    // Goal:  Flip the state of the target qubit if the query register is in the state described by the given bit pattern
    //        (true represents qubit state One, and false represents Zero).
    //        Leave the state of the target qubit unchanged if the query register is in any other state.
    //        Leave the query register in the same state it started in.
    // Example:
    //        If the bit pattern is [true, false], you need to flip the target qubit if and only if the qubits are in the |10⟩ state.
    operation Oracle_ArbitraryPattern (queryRegister : Qubit[], target : Qubit, pattern : Bool[]) : Unit {
        
        body (...) {
            // The following line enforces the constraint on the input arrays.
            // You don't need to modify it. Feel free to remove it, this won't cause your code to fail.
            EqualityFactI(Length(queryRegister), Length(pattern), "Arrays should have the same length");

            (ControlledOnBitString(pattern,X))(queryRegister, target);
        }
        
        adjoint self;
    }
    
    
    // Task 1.4*. Oracle converter
    // Input:  A marking oracle: an oracle that takes a register and a target qubit and
    //         flips the target qubit if the register satisfies a certain condition
    // Output: A phase-flipping oracle: an oracle that takes a register and
    //         flips the phase of the register if it satisfies this condition
    //
    // Note: Grover's algorithm relies on the search condition implemented as a phase-flipping oracle,
    // but it is often easier to write a marking oracle for a given condition. This transformation
    // allows to convert one type of oracle into the other. The transformation is described at
    // https://en.wikipedia.org/wiki/Grover%27s_algorithm, section "Description of Uω".
    // I.e. By bringing the target qubit into superposition |-> = 1/sqrt(2)(|0>-|1>) this flips 
    // to 1/sqrt(2)(|1>-|0>), if f(x)==1 -> we regard the target bit unchanged and the register to be multiplicated 
    // with (-1)^f(x) and this is what Grover needs.
    function OracleConverter (markingOracle : ((Qubit[], Qubit) => Unit is Adj)) : (Qubit[] => Unit is Adj) {
        
        // Hint: Remember that you can define auxiliary operations.
        
        return OracleConverterImpl(markingOracle, _);
    }
    
    operation OracleConverterImpl(markingOracle : ((Qubit[], Qubit) => Unit is Adj), register:Qubit[]) : Unit is Adj {
        using (target = Qubit()) {
            // Put the target into the |-⟩ state
            X(target);
            H(target);
            
            // apply oracle function
            markingOracle(register, target);

            // cleanup target before relase
            H(target);
            X(target);
        }

    }
    
    //////////////////////////////////////////////////////////////////
    // Part II. The Grover iteration
    //////////////////////////////////////////////////////////////////
    
    // Task 2.1. The Hadamard transform
    // Input: A register of N qubits in an arbitrary state
    // Goal:  Apply the Hadamard transform to each of the qubits in the register.
    //
    // Note:  If the register started in the |0...0⟩ state, this operation
    //        will prepare an equal superposition of all 2^N basis states.
    operation HadamardTransform (register : Qubit[]) : Unit
    is Adj {
        ApplyToEachA(H, register);
    }
    
    
    // Task 2.2. Conditional phase flip
    // Input: A register of N qubits in an arbitrary state.
    // Goal:  Flip the sign of the state of the register if it is not in the |0...0⟩ state.
    // Example:
    //        If the register is in state |0...0⟩, leave it unchanged.
    //        If the register is in any other basis state, multiply its phase by -1.
    // Note: This operation implements operator 2|0...0⟩⟨0...0| - I.
    operation ConditionalPhaseFlip (register : Qubit[]) : Unit
    is Adj {
    
        // Hint 1: Note that quantum states are defined up to a global phase.
        // Thus the state obtained as a result of this operation is the same
        // as the state obtained by flipping the sign of only the |0...0⟩ state.

        // Flip |0...0> -> |1...1>
        ApplyToEachA(X, register);

        // Condtional Z flips phase if state is |1...1>, Z(|0>)=|0>, Z(|1>=-|1>)
        Controlled Z(Most(register), Tail(register));

        // Undo flip
        ApplyToEachA(X, register);

        // Hint 2: Alternative: You can use the same trick as in the oracle converter task.
            
        // let allZerosOracle = Oracle_ArbitraryPattern(_, _, new Bool[Length(register)]);
        // let flipOracle = OracleConverter(allZerosOracle);
        // flipOracle(register);
    }
    
    
    // Task 2.3. The Grover iteration
    // Inputs:
    //      1) N qubits in an arbitrary state |x⟩ (input/query register)
    //      2) a phase-flipping oracle that takes an N-qubit register and flips
    //         the phase of the state if the register is in the desired state.
    // Goal:  Perform one Grover iteration.
    operation GroverIteration (register : Qubit[], oracle : (Qubit[] => Unit is Adj)) : Unit
    is Adj {
        
        // Hint: A Grover iteration consists of 4 steps:
        //    1) apply the oracle
        //    2) apply the Hadamard transform
        //    3) perform a conditional phase shift
        //    4) apply the Hadamard transform again
            
        oracle(register);
        // apply Grover diffusion operation H, PhaseFlip, H
        HadamardTransform(register);
        ConditionalPhaseFlip(register);
        HadamardTransform(register);
    }
    
    
    //////////////////////////////////////////////////////////////////
    // Part III. Putting it all together: Grover's search algorithm
    //////////////////////////////////////////////////////////////////
    
    // Task 3.1. Grover's search
    // Inputs:
    //      1) N qubits in the |0...0⟩ state,
    //      2) a marking oracle, and
    //      3) the number of Grover iterations to perform.
    // Goal: Use Grover's algorithm to leave the register in the state that is marked by the oracle as the answer
    //       (with high probability).
    //
    // Note: The number of iterations is passed as a parameter because it is defined by the nature of the problem
    // and is easier to configure/calculate outside the search algorithm itself (for example, in the driver).
    operation GroversSearch (register : Qubit[], oracle : ((Qubit[], Qubit) => Unit is Adj), iterations : Int) : Unit {
 
        let phaseOracle = OracleConverter(oracle);
        HadamardTransform(register);

        for (i in 1..iterations) {
            GroverIteration(register, phaseOracle);
        }
    }
    
    
    // Task 3.2. Using Grover's search
    // Goal: Use your implementation of Grover's algorithm from task 3.1 and the oracles from part 1
    //       to find the marked elements of the search space.
    // This task is not covered by a test and allows you to experiment with running the algorithm.
    operation E2E_GroversSearch_Test () : Unit {

        // Hint 1: To check whether the algorithm found the correct answer (i.e., an answer marked as 1 by the oracle), 
        // you can apply the oracle once more to the register after you've measured it and an ancilla qubit,
        // which will calculate the function of the answer found by the algorithm.

        // Hint 2: Experiment with the number of iterations to see how it affects
        // the probability of the algorithm finding the correct answer.

        // Hint 3: You can use the Message function to write the results to the console.

        let invocationNumbers = 100;
        let n=5; // N=2^n
        let N=PowI(2,n);
        let iterations = Ceiling(PI()*Sqrt(IntAsDouble(N))/4.0+0.5);
        for (k in 1..iterations) {
            mutable correct = 0;
            Message("");
            Message("-------------------------------------------------------------------------------------");
            Message("n="+IntAsString(n)+" N="+IntAsString(PowI(2, n))+" with grover iterations set to: "+IntAsString(k));
            Message("-------------------------------------------------------------------------------------");
            Message("Grover Search for |1111...>");
            for (i in 0..invocationNumbers-1) {
                using ((space, result)=(Qubit[n], Qubit())) {
                    GroversSearch(space, Oracle_AllOnes, k);

                    // measure result space
                    let measure = MultiM(space);
                    Oracle_AllOnes(space, result);
                    if (M(result)==One) {
    //                    Message("found |1111...>");
                        set correct += 1;
                    }
                    else {
    //                    Message ("wrong result: ");
                    }
    //                DumpRegister((), space);

                    ResetAll(space+ [result]);
                }
            }
            Message(DoubleAsStringWithFormat(IntAsDouble(correct)/IntAsDouble(invocationNumbers), "correct results with {0}% prob"));

            set correct = 0;
            Message("Grover Search for |1010...>");
            for (i in 0..invocationNumbers-1) {
                using ((space, result)=(Qubit[n], Qubit())) {
                    GroversSearch(space, Oracle_AlternatingBits, k);

                    // measure result space
                    let measure = MultiM(space);
                    Oracle_AlternatingBits(space, result);
                    if (M(result)==One) {
    //                    Message("found |1010...>");
                        set correct += 1;
                    }
                    else {
    //                    Message ("wrong result: ");
                    }
    //                DumpRegister((), space);

                    ResetAll(space+ [result]);
                }
            }
            Message(DoubleAsStringWithFormat(IntAsDouble(correct)/IntAsDouble(invocationNumbers), "correct results with {0}% prob"));

            set correct = 0;
            let pattern = IntAsBoolArray(Microsoft.Quantum.Random.DrawRandomInt(0, PowI(2,n)-1), n);

            Message("Grover Search for |"+IntAsString(BoolArrayAsInt(pattern))+">");
            for (i in 0..invocationNumbers-1) {
                using ((space, result)=(Qubit[n], Qubit())) {
                    GroversSearch(space, Oracle_ArbitraryPattern( _, _, pattern), k);

                    // measure result space
                    let measure = MultiM(space);
                    Oracle_ArbitraryPattern(space, result, pattern);
                    if (M(result)==One) {
    //                    Message("found |"+IntAsString(BoolArrayAsInt(pattern))+">");
                        set correct += 1;
                    }
                    else {
    //                    Message ("wrong result: ");
                    }
    //                DumpRegister((), space);

                    ResetAll(space+ [result]);
                }
            }
            Message(DoubleAsStringWithFormat(IntAsDouble(correct)/IntAsDouble(invocationNumbers), "correct results with {0}% prob"));
        }
    }
}
