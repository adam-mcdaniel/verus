{
    type MaybeNum = {Some(Num) | None};

    let div n:Num, d:Num =
        if d == 0 then MaybeNum of None
        else MaybeNum of Some (n / d);

    let test_div n:Num, d:Num = 
        match div n d with
            case of Some(result) => print (n as Str)
                                    & " / "
                                    & (d as Str)
                                    & " = "
                                    & (result as Str),
            case of None => print (n as Str)
                                    & " / "
                                    & (d as Str)
                                    & " is undefined";
    test_div 10 2;
    test_div 10 0;
}