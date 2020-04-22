method f(x0: int,y: int) returns (r: int)
requires y >= x0 && y > 0 && x0 >= 0
ensures r == y - x0
{
    var x := x0;
    var d := 0;
    while x < y
    invariant d <= x && x <= y && x0 + d == x 
    // The result of bubbling up on the path from requires to invariant is:
    // y >= x0 -> 0<= x0 ^ x0 <y x0 + 0 == x0 ^ y>=x0
    // The result of bubbling up on the path from invariant to invariant is:
    // d <= x ^ x <= y ^ x0 + d == x  ->  x < y  ->  d + 1 <= x + 1 ^ x + 1 <= y ^ x0 + d + 1 == x + 1  
    // The result of bubbling up on the path from invariant to ensures is:
    // d <= x ^ x <= y ^ x0 + d == x  ->  y <= x  ->  d == y - x0
    decreases y - x
    {
        x := x + 1;
        d := d + 1;
    }
    return d;
}

//Problem 2
method g(x: int) returns (r: int)
requires x > 0
ensures r == x * 2
{
    var y := 0;
    var i := 0;
    while i < x
    invariant i <= x && y % 2 == 0 && y == i * 2
    // The result of bubbling up on the path from requires to invariant is:
    // x > 0  ->  0 <= x ^ 0 % 2 == 0 ^ 0 == 0 * 2
    // The result of bubbling up on the path from invariant to invariant is:
    // i <= x ^ y % 2 == 0 ^ y == i * 2  ->  i < x  ->  (i+1) <= x ^ (y+2) % 2 == 0 ^ (y+2) == (i+1) * 2
    // The result of bubbling up on the path from invariant to ensures is:
    // i <= x ^ y % 2 == 0 ^ y == i * 2  ->  i >= x  ->  y == x * 2 
    decreases x - i
    {
        y := y + 2;
        i := i + 1;
    }
    return y;
}


//Problem 3
method h(x0: int, y0: int) returns (r: int)
requires x0 > 0 && y0 >= 0
ensures x0 % 2 == 0 ==> r == (x0 / 2) + y0  && x0 % 2 != 0 ==> r == (x0 / 2) + y0 + 1
{
    var x := x0;
    var y := y0;
    while x > 0
    invariant x >= -1 
    decreases x
    {
        x := x - 2;
        y := y + 1;
    }
    return y;
}