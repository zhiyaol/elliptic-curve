namespace ECP_resEst {
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.ResourceEstimation;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Unstable.Arithmetic;
    open Microsoft.Quantum.Unstable.TableLookup;
    open Microsoft.Quantum.Diagnostics;


    @EntryPoint()
    operation main() : Unit {
        let num_bits = 256;
        let num_window = 16;

        // input points
        let p_x : Int = 8;
        let p_y : Int = 9;

        // convert input points to binary
        let bin_p_x = IntAsBoolArray(p_x, num_bits);
        let bin_p_y = IntAsBoolArray(p_y, num_bits);

        // qubits in the main routine
        use contrl_qubits = Qubit[num_bits];
        use input_x = Qubit[num_bits];
        use input_y = Qubit[num_bits];

        // initialize qubits; control qubit all in |+> state
        // load binary x and y into qubits
        for i in 0..num_bits-1 {
            H(contrl_qubits[i]);
            if (bin_p_x[i]) {
                X(input_x[i]);
            }
            if (bin_p_y[i]) {
                X(input_y[i]);
            }
        }

        // i-th window operation
        for i in 0..num_window-1 {
            let start = i * (num_bits / num_window);
            let end = (i + 1) * (num_bits / num_window) - 1;
            let control_interval = contrl_qubits[start .. end];
            WindowStep(control_interval, input_x, input_y);
        }

        // inverse QFT on control qubits
        Adjoint ApplyQFT(contrl_qubits);

        // measure control qubits, so now we have 'c'
        for i in 0..num_bits-1 {
            MResetZ(contrl_qubits[i]);
        }

        // second phase estimation to get 'ck'
        // just repeat the above steps
    }

    operation WindowStep(control: Qubit[], x: Qubit[], y: Qubit[]) : Unit {
        let n= Length(x);
        Fact(Length(x) == Length(y), "x and y must be of same size");

        use a = Qubit[n];
        use b = Qubit[n];
        use lambda_r = Qubit[n];


        // TODO: don't trust the following part here.
        let data: Bool[][] = []; // TODO: compute

        within {
            Select(data, control, a + b + lambda_r);
        } apply {
            ECPointAdd(a, b, x, y, lambda_r);
        }
    }

    operation ECPointAdd(a: Qubit[], b: Qubit[], x: Qubit[], y: Qubit[], lambda_r: Qubit[]) : Unit {
        // input: a, b, x, y, lambda_r
        let n= Length(x);
        use z_1 = Qubit[n];
        use z_2 = Qubit[n];
        use z_3 = Qubit[n];
        use z_4 = Qubit[n];
        use lambda = Qubit[n];

        use f = Qubit[4];
        use control = Qubit[1]; //  Zhiyao edited how control is allocated here and in steps functions. Will explain.
        
        step_one(f, control, a, b, x, y, z_1, z_2, z_3, z_4, lambda, lambda_r);
        step_two(f, control, a, b, x, y, z_1, z_2, z_3, z_4, lambda, lambda_r);
        step_three(f, control, a, b, x, y, z_1, z_2, z_3, z_4, lambda, lambda_r);
        step_four(f, control, a, b, x, y, z_1, z_2, z_3, z_4, lambda, lambda_r);
        step_five(f, control, a, b, x, y, z_1, z_2, z_3, z_4, lambda, lambda_r);
        step_six(f, control, a, b, x, y, z_1, z_2, z_3, z_4, lambda, lambda_r);
    }


    operation step_one(f: Qubit[], control: Qubit[], a: Qubit[], b: Qubit[],
                       x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                       z_3: Qubit[], z_4: Qubit[], lambda: Qubit[], lambda_r: Qubit[]) : Unit {
        // step 1

    }

    operation step_two(f: Qubit[], control: Qubit[], a: Qubit[], b: Qubit[],
                       x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                       z_3: Qubit[], z_4: Qubit[], lambda: Qubit[], lambda_r: Qubit[]) : Unit {
        // step 2
        ModSub(a,x);
        Controlled ModSub(control, (b, y)); // Not sure how to do controlled operation

        within {
            ModInv(x,z_1,z_2);
            ModMult(x,y,z_3,z_4);
        } apply {
            
        }

    }

    operation step_three(f: Qubit[], control: Qubit[], a: Qubit[], b: Qubit[],
                       x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                       z_3: Qubit[], z_4: Qubit[], lambda: Qubit[], lambda_r: Qubit[]) : Unit {
        // step 3

    }

    operation step_four(f: Qubit[], control: Qubit[], a: Qubit[], b: Qubit[],
                       x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                       z_3: Qubit[], z_4: Qubit[], lambda: Qubit[], lambda_r: Qubit[]) : Unit {
        // step 4

    }
    

    operation step_five(f: Qubit[], control: Qubit[], a: Qubit[], b: Qubit[],
                       x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                       z_3: Qubit[], z_4: Qubit[], lambda: Qubit[], lambda_r: Qubit[]) : Unit {
        // step 5
        // Adjoint ;
        Controlled ModNeg(control,x);
        ModAdd(a,x); 
    
                       }

    operation step_six(f: Qubit[], control: Qubit[], a: Qubit[], b: Qubit[],
                       x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                       z_3: Qubit[], z_4: Qubit[], lambda: Qubit[], lambda_r: Qubit[]) : Unit {
        // step 6

    }


    // the following section is for the six modular arithmetic operations
    operation ModAdd(x: Qubit[], y: Qubit[]): Unit 
    is Adj + Ctl { // Zhiyao added this line so the function can be controlled and adjointedGIT 
        // x, y are the two numbers to be added
        // the result is stored in y
        // |y> -> |y + x mod p>
    }

    operation ModSub(x: Qubit[], y: Qubit[]): Unit 
    is Adj + Ctl {
        // x, y are the two numbers to be subtracted
        // the result is stored in y
        // |y> -> |y - x mod p>
        ModAdd(x,y);
        
    }

    operation ModNeg(x: Qubit[]): Unit 
    is Adj + Ctl {
        // x is the number to be negated
        // the result is stored in x
        // |x> -> |-x mod p>
    }

    operation ModDbl(x: Qubit[]): Unit 
    is Adj + Ctl {
        // x is the number to be squared
        // the result is stored in x
        // |x> -> |2x mod p>
    }

    operation ModMult(x: Qubit[], y: Qubit[], garb: Qubit[], modMultResult: Qubit[]): Unit 
    is Adj + Ctl{
        // x, y are the two numbers to be multiplied
        // the result is stored in modMultResult
        // modMultResult = |0> -> |xy mod p>
        let n = Length(x);
        Fact(n == Length(y), "x and y must be of same size");



        // there will a ModMultStep operation that is called multiple times
    }

    operation ModInv(x: Qubit[], garb_1: Qubit[], garb_2: Qubit[]): Unit 
    is Adj + Ctl {
        // x is the number to be inverted
        // the result is stored in x
        // |x> -> |x^-1 mod p>
    }

    operation nQubitToff(ctl: Qubit[], target: Qubit, color: Bool): Unit {
        // n-qubit Toffoli gate
        // color is the color of the Toffoli gate
        // color = true: black Toffoli gate
        // color = false: white Toffoli gate
        let n = Length(ctl);

        if color {
            Controlled X(ctl, (target));
        } else {
            for i in 0..n-1 {
                X(ctl[i]);
            }
            Controlled X(ctl, (target));
            for i in 0..n-1 {
                X(ctl[i]);
            }
        }
    }

    operation nQubitEqual(x: Qubit[], y: Qubit[], target: Qubit): Unit {
        // check if two n-qubit numbers are equal
        // Then apply a CNOT gate to target qubit
        let n = Length(x);
        Fact(n == Length(y), "x and y must be of same size");

        use ancilla = Qubit[n];

        for i in 0..n-1 {
            CNOT(x[i], ancilla[i]);
            CNOT(y[i], ancilla[i]);
        }
        // By now, ancilla[i] is 0 if x[i] == y[i], and 1 otherwise.

        // if ancilla[i] is 0 for all i, then x == y, apply X gate to target
        nQubitToff(ancilla, target, false);

        // Uncompute the ancilla qubits
        for i in 0..n-1 {
            CNOT(y[i], ancilla[i]);
            CNOT(x[i], ancilla[i]);
        }

        // reset ancilla qubits and release them without any entanglement.
        for i in 0..n - 1 {
            if (MResetZ(ancilla[i]) == One) {
                fail "Ancilla qubit was not in the |0> state upon reset.";
            }
        }
    }
}

