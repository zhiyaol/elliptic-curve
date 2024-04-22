namespace ECP_resEst {
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.ResourceEstimation;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Unstable.Arithmetic;
    open Microsoft.Quantum.Unstable.TableLookup;

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
            let c_offset = start; // c + 2^start to account for the next batch of c. 
            WindowStep(control_interval, input_x, input_y, c_offset);
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

    operation WindowStep(control: Qubit[], x: Qubit[], y: Qubit[], c_offset:Int) : Unit {
        let n= Length(x);
        // Fact(Length(x) == Length(y), "x and y must be of same size");

        use a = Qubit[n];
        use b = Qubit[n];
        use lambda_r = Qubit[n];

        // TODO: Look up table
        let data: Bool[][] = [[], size = 2^Length(control)]; // Is this size set up correctly?
        let precision = Length(x);

        for c0 in 0..2^Length(control)-1 { //[c]R = R+R+...+R (add it c times)
        
            let c = c0 + 2^c_offset; // account for the next batch of c. c_offset is passed in at the i-th window operation step.
            // How to keep track of the (a,b) calculated in the previous batch?

            if c == 0 {
                let result_a: Int = 0; 
                let result_b: Int = 0;
            }
            elif c == 1 {
                let result_a: Int = Rx; // Placeholder
                let result_b: Int = Ry;
            }
            else {
                let result_a: Int = c^3; // Placeholder
                let result_b: Int = c + 1; // Placeholder
            }

            let result_lambda_r: Int = (3*result_a^2+c1)/(2*result_b); //c1 is the eliptic curve parameter

            let bin_a = IntAsBoolArray(result_a, precision);
            let bin_b = IntAsBoolArray(result_b, precision);

            let bin_lambda_r = IntAsBoolArray(result_lambda_r, precision);

            set data w/= c <- (bin_a + bin_b + bin_lambda_r); 
            // Set up as look up lambda_r from c. 
            // Could also change to lambda_r from a,b but would probably require two lookup tables instead of 1
        }
    
        within { 
            // control are the c input qubits
            Select(data, control, a + b + lambda_r);

        } apply {
            ECPointAdd(a, b, x, y, lambda_r);
        }
    }

    operation Select(data : Bool[][], address : Qubit[], target : Qubit[]) : Unit is Adj + Ctl{}

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
            Controlled X([f[0]]+control, ancilla); 
            for i in 1..Length(z_4)-1 {
                nQubitToff(control+[z_4[i]],lambda[i],True); 
                }

            X(f[0]);
            CNOT(control[0],ancilla); // Check implementation with mentors here
            
            for i in 1..Length(lambda)-1 {
                nQubitToff(control+[lambda_r[i]],lambda[i],True);
                }

            nQubitEqual(lambda,lambda_r,f[0])
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

        Adjoint step_five_helper(control,x,y,z_1,z_2,z_3,z_4,lambda);
        
        Controlled ModNeg(control,x);
        ModAdd(a,x); 
        Controlled ModSub(control,(b,y));
    }

    operation step_five_helper(control: Qubit[], x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                                z_3: Qubit[], z_4: Qubit[], lambda: Qubit[]) : Unit
    is Adj + Ctl {
    // Helper Function that fits in the uncompute box in step 5
        within {
            ModInv(x,z_1,z_2);
            ModMult(x,y,z_3,z_4);
        } apply {
            for i in 1..Length(z_4)-1 {
                nQubitToff(control+[z_4[i]],lambda[i],true);
                }
        }
    }

    operation step_six(f: Qubit[], control: Qubit[], a: Qubit[], b: Qubit[],
                       x: Qubit[], y: Qubit[], z_1: Qubit[], z_2: Qubit[], 
                       z_3: Qubit[], z_4: Qubit[], lambda: Qubit[], lambda_r: Qubit[]) : Unit {
        // step 6

    }


    // the following section is for the six modular arithmetic operations
    operation ModAdd(x: Qubit[], y: Qubit[]): Unit 
    is Adj + Ctl { // Zhiyao added this line so the function can be controlled and adjointed
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


        // there will a ModMultStep operation that is called multiple times
    }

    operation ModInv(x: Qubit[], garb_1: Qubit[], garb_2: Qubit[]): Unit 
    is Adj + Ctl {
        // x is the number to be inverted
        // the result is stored in x
        // |x> -> |x^-1 mod p>
    }
}

