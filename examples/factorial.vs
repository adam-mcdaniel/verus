{
    let factorial = \n: Num -> product (range 1 n + 1);

    let n = (args())@1 as Num;
    let result = factorial n;
    print "Factorial of " & (n as Str) & " is " & (result as Str);
}