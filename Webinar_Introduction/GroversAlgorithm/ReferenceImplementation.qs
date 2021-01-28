// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT license.

//////////////////////////////////////////////////////////////////////
// This file contains reference solutions to all tasks.
// The tasks themselves can be found in Tasks.qs file.
// We recommend that you try to solve the tasks yourself first,
// but feel free to look up the solution if you get stuck.
//////////////////////////////////////////////////////////////////////

namespace Quantum.Kata.GroversAlgorithm {
    
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;

    
    //////////////////////////////////////////////////////////////////
    // Part I. Oracles for Grover's Search
    //////////////////////////////////////////////////////////////////
    
    // Task 1.1. The |11...1⟩ oracle
    operation Oracle_AllOnes_Reference (queryRegister : Qubit[], target : Qubit) : Unit is Adj {        
        Controlled X(queryRegister, target);
    }
    
    
    // Task 1.2. The |1010...⟩ oracle
    operation Oracle_AlternatingBits_Reference (queryRegister : Qubit[], target : Qubit) : Unit
    is Adj {
        
        within {
            // flip the bits in odd (0-based positions),
            // so that the condition for flipping the state of the target qubit is "query register is in 1...1 state"
            for (i in 1 .. 2 .. Length(queryRegister) - 1) {
                X(queryRegister[i]);
            }
        }
        apply {
            Controlled X(queryRegister, target);
        }
    }
    
    
    // Task 1.3. Arbitrary bit pattern oracle
    operation Oracle_ArbitraryPattern_Reference (queryRegister : Qubit[], target : Qubit, pattern : Bool[]) : Unit is Adj {        
        (ControlledOnBitString(pattern, X))(queryRegister, target);
    }
    
    
    // Task 1.4*. Oracle converter
    operation OracleConverterImpl_Reference (markingOracle : ((Qubit[], Qubit) => Unit is Adj), register : Qubit[]) : Unit is Adj {
        using (target = Qubit()) {
            within {
                // Put the target into the |-⟩ state
                X(target);
                H(target);
            } apply {
                // Apply the marking oracle; since the target is in the |-⟩ state,
                // flipping the target if the register satisfies the oracle condition will apply a -1 factor to the state
                // (phase kickback trick)
                markingOracle(register, target);
            }
        }
    }
    
    
    function OracleConverter_Reference (markingOracle : ((Qubit[], Qubit) => Unit is Adj)) : (Qubit[] => Unit is Adj) {
        return OracleConverterImpl_Reference(markingOracle, _);
    }
    
    
    //////////////////////////////////////////////////////////////////
    // Part II. The Grover iteration
    //////////////////////////////////////////////////////////////////
    
    // Task 2.1. The Hadamard transform
    operation HadamardTransform_Reference (register : Qubit[]) : Unit is Adj {
        
        ApplyToEachA(H, register);

        // ApplyToEach is a library routine that is equivalent to the following code:
        // for (qubit in register) {
        //     H(qubit);
        // }
    }
    
    
    // Task 2.2. Conditional phase flip
    operation ConditionalPhaseFlip_Reference (register : Qubit[]) : Unit is Adj {
        // Define a marking oracle which detects an all zero state
        let allZerosOracle = Oracle_ArbitraryPattern_Reference(_, _, new Bool[Length(register)]);
            
        // Convert it into a phase-flip oracle and apply it
        let flipOracle = OracleConverter_Reference(allZerosOracle);
        flipOracle(register);
    }
    
    
    operation PhaseFlip_ControlledZ (register : Qubit[]) : Unit is Adj {
        // Alternative solution, described at https://quantumcomputing.stackexchange.com/questions/4268/how-to-construct-the-inversion-about-the-mean-operator/4269#4269
        within {
            ApplyToEachA(X, register);
        } apply {
            Controlled Z(Most(register), Tail(register));
        }
    }
    
    
    // Task 2.3. The Grover iteration
    operation GroverIteration_Reference (register : Qubit[], oracle : (Qubit[] => Unit is Adj)) : Unit is Adj {
        oracle(register);
        HadamardTransform_Reference(register);
        ConditionalPhaseFlip_Reference(register);
        HadamardTransform_Reference(register);
    }
    
    
    //////////////////////////////////////////////////////////////////
    // Part III. Putting it all together: Grover's search algorithm
    //////////////////////////////////////////////////////////////////
    
    // Task 3.1. Grover's search
    operation GroversSearch_Reference (register : Qubit[], oracle : ((Qubit[], Qubit) => Unit is Adj), iterations : Int) : Unit is Adj {
        
        let phaseOracle = OracleConverter_Reference(oracle);
        HadamardTransform_Reference(register);
            
        for (i in 1 .. iterations) {
            GroverIteration_Reference(register, phaseOracle);
        }
    }
    
}

    // open Microsoft.Quantum.Math;
    // open Microsoft.Quantum.Convert;
    // open Microsoft.Quantum.Measurement;

    // Task 3.2. Using Grover's search
    // Goal: Use your implementation of Grover's algorithm from task 3.1 and the oracles from part 1
    //       to find the marked elements of the search space.
    // This task is not covered by a test and allows you to experiment with running the algorithm.
//     operation E2E_GroversSearch_Test () : Unit {

//         // Hint 1: To check whether the algorithm found the correct answer (i.e., an answer marked as 1 by the oracle), 
//         // you can apply the oracle once more to the register after you've measured it and an ancilla qubit,
//         // which will calculate the function of the answer found by the algorithm.

//         // Hint 2: Experiment with the number of iterations to see how it affects
//         // the probability of the algorithm finding the correct answer.

//         // Hint 3: You can use the Message function to write the results to the console.

//         let invocationNumbers = 100;
//         let n=5; // N=2^n
//         let N=PowI(2,n);
//         let iterations = Ceiling(PI()*Sqrt(IntAsDouble(N))/4.0+0.5);
//         for (k in 1..iterations) {
//             mutable correct = 0;
//             Message("");
//             Message("-------------------------------------------------------------------------------------");
//             Message("n="+IntAsString(n)+" N="+IntAsString(PowI(2, n))+" with grover iterations set to: "+IntAsString(k));
//             Message("-------------------------------------------------------------------------------------");
//             Message("Grover Search for |1111...>");
//             for (i in 0..invocationNumbers-1) {
//                 using ((space, result)=(Qubit[n], Qubit())) {
//                     GroversSearch(space, Oracle_AllOnes, k);

//                     // measure result space
//                     let measure = MultiM(space);
//                     Oracle_AllOnes(space, result);
//                     if (M(result)==One) {
//     //                    Message("found |1111...>");
//                         set correct += 1;
//                     }
//                     else {
//     //                    Message ("wrong result: ");
//                     }
//     //                DumpRegister((), space);

//                     ResetAll(space+ [result]);
//                 }
//             }
//             Message(DoubleAsStringWithFormat(IntAsDouble(correct)/IntAsDouble(invocationNumbers), "correct results with {0}% prob"));

//             set correct = 0;
//             Message("Grover Search for |1010...>");
//             for (i in 0..invocationNumbers-1) {
//                 using ((space, result)=(Qubit[n], Qubit())) {
//                     GroversSearch(space, Oracle_AlternatingBits, k);

//                     // measure result space
//                     let measure = MultiM(space);
//                     Oracle_AlternatingBits(space, result);
//                     if (M(result)==One) {
//     //                    Message("found |1010...>");
//                         set correct += 1;
//                     }
//                     else {
//     //                    Message ("wrong result: ");
//                     }
//     //                DumpRegister((), space);

//                     ResetAll(space+ [result]);
//                 }
//             }
//             Message(DoubleAsStringWithFormat(IntAsDouble(correct)/IntAsDouble(invocationNumbers), "correct results with {0}% prob"));

//             set correct = 0;
//             let pattern = IntAsBoolArray(Microsoft.Quantum.Random.DrawRandomInt(0, PowI(2,n)-1), n);

//             Message("Grover Search for |"+IntAsString(BoolArrayAsInt(pattern))+">");
//             for (i in 0..invocationNumbers-1) {
//                 using ((space, result)=(Qubit[n], Qubit())) {
//                     GroversSearch(space, Oracle_ArbitraryPattern( _, _, pattern), k);

//                     // measure result space
//                     let measure = MultiM(space);
//                     Oracle_ArbitraryPattern(space, result, pattern);
//                     if (M(result)==One) {
//     //                    Message("found |"+IntAsString(BoolArrayAsInt(pattern))+">");
//                         set correct += 1;
//                     }
//                     else {
//     //                    Message ("wrong result: ");
//                     }
//     //                DumpRegister((), space);

//                     ResetAll(space+ [result]);
//                 }
//             }
//             Message(DoubleAsStringWithFormat(IntAsDouble(correct)/IntAsDouble(invocationNumbers), "correct results with {0}% prob"));
//         }
//     }
// }

