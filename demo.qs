

namespace Test {
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Unstable.TableLookup;

    @EntryPoint()
    operation Run() : Unit {
        let precision = 15;

        // compute c^3 and c+1 from c = 8..15 into each 15 bits

        // window_step : {0,1}^16 -> {0,1}^(256*3)

        // data = [bin(0^3), bin(1^3), bin(2^3), ...]
        // represents {0,1}^3 -> {0,1}^15
        mutable data: Bool[][] = [[], size = 8];

        for c in 0..7 {
            let result: Int = c^3;
            let result2: Int = c + 1;
            let binResult = IntAsBoolArray(result, precision);
            let binResult2 = IntAsBoolArray(result2, precision);

            set data w/= c <- (binResult + binResult2);
        }

        Message($"data = {data}");

        use address = Qubit[3];
        use target = Qubit[2 * precision];

        H(address[0]);

        Select(data, address, target);

        DumpMachine();

        ResetAll(address + target);
    }

    operation WindowStep(control: Qubit[], x: Qubit[], y: Qubit[]) : Unit {
        let n = Length(x);
        Fact(n == Length(y), "x and y must be of same size");

        use a = Qubit[n];
        use b = Qubit[n];
        use lambda = Qubit[n];

        let data: Bool[][] = []; // TODO: compute

        within {
            Select(data, control, a + b + lambda);
        } apply {
            ECPointAdd(a, b, x, y, lambda);
        }
    }

    operation SWAP(a : Qubit, b : Qubit) : Unit is Ctl {
        within {
            CNOT(a, b);
        } apply {
            CNOT(b, a);
        }
    }

    operation Fredkin(ctl: Qubit, target1 : Qubit, target2 : Qubit) : Unit {
        Controlled SWAP([ctl], (target1, target2));
    }
}

