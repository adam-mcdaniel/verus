{
    type Point = {
        x: Num,
        y: Num
    };

    let p: Point = {x: 5, y: 6};

    let move p:Point, dx:Num, dy:Num = {x: p@x + dx, y: p@y + dy};
    let p2 = move p 1 2;

    print p2;
}