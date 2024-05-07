namespace ECP_resEst {
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.ResourceEstimation;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Unstable.Arithmetic;
    open Microsoft.Quantum.Unstable.TableLookup;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Unstable.Arithmetic;

    function get_p() : BigInt {
        let p : BigInt = 256L;
        return p;
    }

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
        // the qubit arithmetic follows little endian convention
        // the least significant bit is at the first qubit
        // the most significant bit is at the last qubit
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

        // for c in 0,...,2^windowSize - 1
        // compute (a, b) = [c]R and lambda_r = (3a^2 + c_1)/(2b)
        // (R is the basis point)
        // then set data w/= c <- (binResult + binResult2) // which means data[c] = [a, b, lambda_r]

        // then do the look up with address = |+>^16
        // since the address is in superposition, the target qubit will also be in superposition
        // target qubit = a + b + lambda_r
        // Select(data, address, target)  // which means target qubit = data[address]

        within {
            Select(data, control, a + b + lambda_r);
        } apply {
            ECPointAdd(a, b, x, y, lambda_r);
        }

        // for each window, we need to change the basis point R.
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
        use control = Qubit[1];
        
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
        nQubitEqual(a, x, f[0]);

        ModNeg(y);

        nQubitEqual(b, y, f[1]);
        ModNeg(y);

        nQubitToff(a + b, f[2], false);
        nQubitToff(x + y, f[3], false);
        nQubitToff(f[1..3], control[0], false);
    }

    operation step_two(f: Qubit[], control: Qubit[], a: Qubit[], b: Qubit[],
                       x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                       z_3: Qubit[], z_4: Qubit[], lambda: Qubit[], lambda_r: Qubit[]) : Unit {
        // step 2
        ModSub(a,x);
        Controlled ModSub(control, (b, y)); 

        within {
            ModInv(x,z_1,z_2);
            ModMult(x,y,z_3,z_4);
        } apply {
            use ancilla = Qubit();
            X(f[0]);
            Controlled X([f[0]]+control, ancilla); // Unsure how I concatenate qubit lists and qubits into one list.
            for i in 1..Length(z_4)-1 {
                nQubitToff(control+[z_4[i]], lambda[i], true); // Unsure how I concatenate qubit lists and qubits into one list
            }

            X(f[0]);
            CNOT(control[0],ancilla); // Check implementation with mentors here
            
            for i in 1..Length(lambda)-1 {
                nQubitToff(control+[lambda_r[i]], lambda[i], true); // Unsure how I concatenate qubit lists and qubits into one list
            }

            nQubitEqual(lambda,lambda_r,f[0])
        }
    }

    operation step_three(f: Qubit[], control: Qubit[], a: Qubit[], b: Qubit[],
                       x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                       z_3: Qubit[], z_4: Qubit[], lambda: Qubit[], lambda_r: Qubit[]) : Unit {
        // step 3
        let n = Length(x);
        
        within {
            ModMult(x, lambda, z_2, z_1)
        }
        apply {
            Controlled ModSub(control, (z_1, y))
        }

        within {
            for i in 0..n-1 {
                CNOT(a[i], z_1[i]);
            }
            ModDbl(z_1);
            ModAdd(a, z_1);
        }
        apply {
            Controlled ModAdd(control, (z_1, x));
        }
    }

    operation step_four(f: Qubit[], control: Qubit[], a: Qubit[], b: Qubit[],
                       x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                       z_3: Qubit[], z_4: Qubit[], lambda: Qubit[], lambda_r: Qubit[]) : Unit {
        // step 4
        let n = Length(x);
        within {
            for i in 0..n-1 {
                CNOT(lambda[i], z_4[i]);
            }
            ModMult(lambda, z_4, z_2, z_3);
        }
        apply {
            ModSub(z_3, x);
        }

        within {
            ModMult(x, lambda, z_4, z_3);
        }
        apply {
            for i in 0..n-1 {
                CNOT(z_3[i], y[i]);
            }
        }
    }
    

    operation step_five(f: Qubit[], control: Qubit[], a: Qubit[], b: Qubit[],
                       x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                       z_3: Qubit[], z_4: Qubit[], lambda: Qubit[], lambda_r: Qubit[]) : Unit {
        // step 5
        Adjoint step_five_helper(control,x,y,z_1,z_2,z_3,z_4,lambda);
        
        Controlled ModNeg(control,x);
        ModAdd(a,x); 
        Controlled ModSub(control,(b,y));
    }

    operation step_five_helper(control: Qubit[], x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                                z_3: Qubit[], z_4: Qubit[], lambda: Qubit[]) : Unit is Adj + Ctl {
    // Helper Function that fits in the uncompute box in step 5
        within {
            ModInv(x,z_1,z_2);
            ModMult(x,y,z_3,z_4);
        } apply {
            for i in 1..Length(z_4)-1 {
                nQubitToff(control+[z_4[i]], lambda[i], true);
            }
        }
    }

    operation step_six(f: Qubit[], control: Qubit[], a: Qubit[], b: Qubit[],
                       x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                       z_3: Qubit[], z_4: Qubit[], lambda: Qubit[], lambda_r: Qubit[]) : Unit {
        // step 6
        nQubitToff(f[1..3], control[0], false);
        for i in 0..Length(x)-1 {
            CCNOT(f[3], a[i], x[i]);
        }
        for i in 0..Length(x)-1 {
            CCNOT(f[3], b[i], y[i]);
        }

        // check (a, b) = (x, y)
        use ancilla = Qubit[2];
        nQubitEqual(a, x, ancilla[0]);
        nQubitEqual(b, y, ancilla[1]);
        CCNOT(ancilla[0], ancilla[1], f[3]);


        nQubitToff(a + b, f[2], false);
        Controlled ModSub(f[0..1], (a, x));
        Controlled ModSub(f[0..1], (b, y));

        // This is lazy way; can certainly find a more economic way
        nQubitToff(x + y, f[0], false);
        nQubitToff(x + y, f[1], false);
    }


    // the following section is for the six modular arithmetic operations
    operation ModAdd(x: Qubit[], y: Qubit[]): Unit 
    is Adj + Ctl {
        // x, y are the two numbers to be added
        // the result is stored in y
        // |y> -> |y + x mod p>

        use ancilla = Qubit[1];
        IncByLE(x, y + ancilla);

        // Add(-p) to y and ancilla
        Adjoint IncByL(get_p(), y + ancilla);
        // controlled by ancilla and add(p) to y
        Controlled IncByL(ancilla, (get_p(), y));
        ApplyIfLessLE(X, x, y, ancilla[0]);

        X(ancilla[0]);
    }

    operation ModSub(x: Qubit[], y: Qubit[]): Unit 
    is Adj + Ctl {
        // x, y are the two numbers to be subtracted
        // the result is stored in y
        // |y> -> |y - x mod p>
        within {
            for i in 0..Length(x)-1 {
                X(x[i]);
            }
            IncByL(get_p() + 1L, x);
        } apply {
            ModAdd(x, y);
        }
    }

    operation ModNeg(x: Qubit[]): Unit 
    is Adj + Ctl {
        // x is the number to be negated
        // the result is stored in x
        // |x> -> |-x mod p>
        use ancilla = Qubit[1];
        nQubitToff(x, ancilla[0], false);
        for i in 0..Length(x)-1 {
            CNOT(ancilla[0], x[i]);
        }
        Controlled IncByL(ancilla, (get_p() + 1L, x));
        nQubitToff(x, ancilla[0], false);
    }

    // Mathias's implementation
    // Computes (xs += xs) mod p
    //
    // References:
    //     - [arXiv:2306.08585](https://arxiv.org/pdf/2306.08585.pdf)
    // |x> -> |2x mod p>
    operation ModDbl(x : Qubit[]): Unit is Adj + Ctl {
        use lsb = Qubit();
        use msb = Qubit();

        Adjoint IncByLUsingIncByLE(RippleCarryCGIncByLE, get_p(), [lsb] + x + [msb]);
        Controlled IncByLUsingIncByLE([msb], (RippleCarryCGIncByLE, get_p(), [lsb] + x));

        CNOT(lsb, msb);
        X(msb);

        CyclicRotateRegister([lsb] + x); 
        // Dropping original most significant qubit in xs. How do we know it's not 1?
    }
    internal operation CyclicRotateRegister(qs : Qubit[]) : Unit is Adj + Ctl {
        // Keep lsb as lsb so doubling actually happens
        SwapReverseRegister(qs); // Uses SWAP gates to Reversed the order of the qubits in a register.
        SwapReverseRegister(Rest(qs)); 
        //Rest: Creates an array that is equal to an input array except that the first array element is dropped.
    }


    operation ModMult(x: Qubit[], y: Qubit[], garb: Qubit[], modMultResult: Qubit[]): Unit 
    is Adj + Ctl{
        // x, y are the two numbers to be multiplied
        // the result is stored in modMultResult
        // modMultResult = |0> -> |xy mod p>
        let n = Length(x);
        Fact(n == Length(y), "x and y must be of same size");

        // for n bits number, there will be n/4 ModMultStep operations
        for step_idx in 0..n/4-1 {
            ModMultStep(x[step_idx*4 .. (step_idx+1)*4-1], y, garb, modMultResult);
        }

        use ancilla = Qubit[1];
        Adjoint IncByL(get_p(), ancilla + modMultResult);
        Controlled IncByL(ancilla, (get_p(), modMultResult));
    }

    operation ModMultStep(x: Qubit[], y: Qubit[], garb: Qubit[], modMultResult: Qubit[]) : 
    Unit is Adj + Ctl {
        Fact(Length(garb) == 4, "garb qubit[] must be of size 4");
        Fact(Length(x) == 4, "x qubit[] is the 4 controlled qubit for addition");

        use ancilla = Qubit[4];

        for i in 0..3 {
            for addition_step in 0..2^i {
                Controlled IncByLE([x[i]], (y, ancilla + modMultResult));
            }
        }
        for i in 0..3 {
            CNOT(modMultResult[i], garb[i]);
        }

        // lookup table
        let precision = Length(x) + 4;
        let lookupTable = get_lookUpTable_modMult(precision);

        use lookUpAncilla = Qubit[precision];
        within {
            Select(lookupTable, garb, lookUpAncilla);
        } apply {
            IncByLE(lookUpAncilla, ancilla + modMultResult);
        }
    }

    function get_lookUpTable_modMult(precision : Int) : Bool[][] {
        mutable table: Bool[][] = [[], size = 17];
        for c in 0..16 {
            mutable result : BigInt = (-1L / get_p()) % 16L * get_p() ;

            let binResult = BigIntAsBoolArray(result, precision);

            set table w/= c <- binResult;
        }
        return table;
    }

    operation ModInv(x: Qubit[], garb_1: Qubit[], garb_2: Qubit[]): Unit 
    is Adj + Ctl {
        // x is the number to be inverted
        // the result is stored in x
        // |x> -> |x^-1 mod p>
        let n = Length(x);

        // specify all the ancilla qubit: v, a, f, u, r, s
        use ancilla_b = Qubit[1];
        use ancilla_a = Qubit[1];
        use ancilla_f = Qubit[1];
        X(ancilla_f[0]);
        
        // initialize |u=p>
        use ancilla_u = Qubit[n];
        let bin_p = BigIntAsBoolArray(get_p(), n);
        for i in 0..n-1 {
            if bin_p[i] {
                X(ancilla_u[i]);
            }
        }

        use ancilla_r = Qubit[n];

        // initialize |s=1>
        use ancilla_s = Qubit[n];
        X(ancilla_s[0]);

        // the block is repeated 2n times
        for modInv_subroutine_idx in 1..2*n {
            use ancilla_m_i = Qubit[1];

            Controlled nQubitToff(ancilla_f, (x, ancilla_m_i[0], false));
            CNOT(ancilla_m_i[0], ancilla_f[0]);

            // the controll qubit is always the lsb of u and x (for all repetitions)
            within {
                X(ancilla_u[0]);                
            } apply {
                CCNOT(ancilla_u[0], ancilla_f[0], ancilla_a[0]);
            }

            within {
                X(ancilla_f[0]);
            } apply {
                nQubitToff(ancilla_a + ancilla_f + [x[0]], ancilla_m_i[0], false);
            }

            CNOT(ancilla_a[0], ancilla_b[0]);
            CNOT(ancilla_m_i[0], ancilla_b[0]);

            // compare: u < v
            // controlled by ancilla_f and ancilla_b (white)
            // controlled NOT by u < v
            within {
                X(ancilla_b[0]);
            } apply {
                Controlled ApplyIfLessLE(ancilla_b + ancilla_f, 
                           (ApplyToEachCA(X, _), ancilla_u, x, [ancilla_a[0], ancilla_m_i[0]]));
            }

            // controlled n-qubit SWAP
            Controlled nQubitSWAP(ancilla_a, (ancilla_u, x));
            Controlled nQubitSWAP(ancilla_a, (ancilla_r, ancilla_s));

            // controlled subtration and addition
            within {
                X(ancilla_b[0]);
            } apply {
                Controlled Adjoint IncByLE(ancilla_b + ancilla_f, (ancilla_u, x));
                Controlled IncByLE(ancilla_b + ancilla_f, (ancilla_r, ancilla_s));
            }

            CNOT(ancilla_a[0], ancilla_b[0]);
            CNOT(ancilla_m_i[0], ancilla_b[0]);

            // controlled halve operation. Swap lsb with msb because we know lsb should be 0
            Controlled nQubitHalve(ancilla_f, x);
            ModDbl(ancilla_r);

            // controlled n-qubit SWAP
            Controlled nQubitSWAP(ancilla_a, (ancilla_u, x));
            Controlled nQubitSWAP(ancilla_a, (ancilla_r, ancilla_s));

            within {
                X(ancilla_s[0]);
            } apply {
                CNOT(ancilla_s[0], ancilla_a[0]);
            }
        }

        // modNeg, the paper made an mistake in Fig.7
        ModNeg(ancilla_r);
        IncByL(get_p(), ancilla_r);
        nQubitSWAP(ancilla_r, x);
    }

    operation nQubitToff(ctl: Qubit[], target: Qubit, color: Bool): Unit is Adj + Ctl{
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

        within {
            for i in 0..n-1 {
                CNOT(x[i], ancilla[i]);
                CNOT(y[i], ancilla[i]);
            }
        } apply {
            nQubitToff(ancilla, target, false);
        }
    }

    // n-qubit swap gate
    operation nQubitSWAP(a : Qubit[], b : Qubit[]) : Unit is Adj + Ctl {
        Fact(Length(a) == Length(b), "a and b must be of same size");
        for i in 0..Length(a)-1 {
            within {
                CNOT(a[i], b[i]);
            } apply {
                CNOT(b[i], a[i]);
            }    
        }
    }

    // n-qubit Fredkin gate
    // single control qubit and apply SWAP gate between two n-qubit registers target1 and target2
    operation nQubitFredkin(ctl : Qubit, target1 : Qubit[], target2 : Qubit[]) : Unit is Adj {
        Controlled nQubitSWAP([ctl], (target1, target2));
    }

    // halve the n-qubit number
    // swap the i-th qubit (represent 2^i) with the (i+1)-th qubit 2^(i+1)
    // this Halve() will swap lsb with msb, use only when we know lsb == 0
    operation nQubitHalve(x : Qubit[]) : Unit is Adj + Ctl {
        for i in 0..Length(x)-1 {
            SWAP(x[i], x[i+1]);
        }
    }
}




