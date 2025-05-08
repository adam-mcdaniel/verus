{
    let factorial = \n: Num -> product (range 1 n + 1);

    match (args ())@1 with
        case of Some(x) => {
            let n = x as Num;
            let result = factorial n;
            print "Factorial of " & (n as Str) & " is " & (result as Str);
        },
        case of None => {
            print "Please provide a number.";
        };
}