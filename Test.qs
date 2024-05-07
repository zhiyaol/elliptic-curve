namespace ECP_test {
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Unstable.Arithmetic;
    open Microsoft.Quantum.ResourceEstimation;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Unstable.TableLookup;
    open Microsoft.Quantum.Diagnostics;


    internal operation TestDblMod(n : Int) : Unit {
        use xs = Qubit[n];

        for p in 3..2..(1 <<< n) - 1 {
            for xsValue in 0..p - 1 {
                ApplyXorInPlace(xsValue, xs);

                ModDbl(IntAsBigInt(p), xs);

                let actual = MeasureInteger(xs);
                let expected = (2 * xsValue) % p;

                Fact(actual == expected, $"unexpected value {actual} for `xs` given xsValue = {xsValue} and p = {p}; expected {expected}");
            }
        }
    }
}