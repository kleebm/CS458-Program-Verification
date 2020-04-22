// The correct_guess predicate takes four parameters:
//   the two guesses, the correct price, and the value the function returns.
// Inside the curly braces should be a logical statetment that evaluates
//   to true if the function returns the correct value, and false if it doesn't.
// The body of the predicate now says "true".  Please modify it appropriately. 
predicate correct_guess(guess1: int, guess2: int, price: int, r: int)
{(guess1 > price && guess2 > price && r == -1) ||
 (guess1 <= price && guess2 > price && r == guess1) || 
 (guess1 > price && guess2 <= price && r == guess2) || 
 (guess1 <= price && guess2 <= price && guess1 > guess2 && r == guess1) || 
 (guess1 <= price && guess2 <= price && guess2 > guess1 && r == guess2) || 
 (guess1 <= price && guess2 <= price && guess1 == guess2 && (r == guess1 || r == guess2))}
//the predicate should check for all situations


// All the following functions take three parameters:
//   the two guesses and the correct price.
// The intention is to return the value required by the assignment.
// They may or may not be correct.
// Do not change the first three functions.
// Modify the body of the fourth function to make it work propoerly.

// Number of paths through guess_price1:
//   3 paths
// Values for which guess_price1 returns the wrong answer:
//  guess1 = 20, guess2 = 10, price = 15, r = -1 (should be 10)
// Result of bubbling up postcondition for path taken by above values:
//assume true
//  assert guess1 > price ^ guess2 > price -> guess_price(guess1, guess2, price, -1) 
//assume guess1 > price & guess2 > price
//  assert correct_guess(guess1, guess2, price, -1)
//best:= -1
//  assert correct_guess(guess1, guess2, price, best)
//r:= best
//  assert correct_guess(guess1, guess2, price, r)
method guess_price1(guess1: int, guess2: int, price: int) returns (r: int)
requires guess1 > 0 && guess2 > 0 && price > 0
ensures correct_guess(guess1, guess2, price, r)
{
  var best;
  if guess1 <= price && guess2 <= price
    {
      best := guess1;
      if guess2 > best
      {
        best := guess2;
      }
    }
  else 
  {
    best := -1;
  }
  return best;
}

// Number of paths through guess_price2:
//  4
// Values for which guess_price2 returns the wrong answer:
//  guess1 = 10, guess2 = 20, price = 15, r = -1 (should be 10)
// Result of bubbling up postcondition for path taken by above values:
//assume true
//  assert guess2 <= guess1 -> price < guess1 -> correct_guess(guess1, guess2,price,-1)
//best:=guess1 
//  assert guess2 <= best -> price < best -> correct_guess(guess1,guess2,price,-1) 
//assume guess2 <= best
//  assert price < best -> correct_guess(guess1,guess2, price, -1) 
//assume price < best
//  asssert correct_guess(guess1,guess2,price,-1)
//r:= -2
//  assert correct_guess(guess1, guess2, price, r)
method guess_price2(guess1: int, guess2: int, price: int) returns (r: int)
requires price > 0 && guess1 > 0 && guess2 > 0
ensures correct_guess(guess1, guess2, price, r)
{
  var best := guess1;
  if guess2 > best
  {
    best := guess2;
  }
  if best <= price
  {
    return best;
  }
  else
  { 
    return -1;
  }
}

// Number of paths through guess_price3:
//   3
// Values for which guess_price3 returns the wrong answer:
//  guess1 = 10, guess2 = 20, price = 15, r = 20  (should be 10)
// Result of bubbling up postcondition for path taken by above values:
//assume True
//  assert guess1<= price || guess2<=price -> guess2>guess1 -> correct_guess(guess1,guess2,price,guess1)
//assume guess1<= price || guess2<= price
//  assert guess2>guess1 -> correct_guess(guess1,guess2,price,guess1)
//best:=guess1
//  assert guess2>best -> correct_guess(guess1,guess2,price,guess2)
//assume guess2> best
//  assert correct_guess(guess1,guess2,price,guess2)
//best:=guess2
//  assert correct_guess(guess1,guess2,price, best)
//r:=best
//  assert correct_guess(guess1,guess2,price,r)
method guess_price3(guess1: int, guess2: int, price: int) returns (r: int)
requires price > 0 && guess1 > 0 && guess2 > 0
ensures correct_guess(guess1, guess2, price, r)
{
  var best;
  if guess1 <= price || guess2 <= price
    {
      best := guess1;
      if guess2 > best
      {
        best := guess2;
      }
    }
  else 
  {
    best := -1;
  }
  return best;
}

method guess_price4(guess1: int, guess2: int, price: int) returns (r: int)
requires price > 0 && guess1 > 0 && guess2 > 0
ensures correct_guess(guess1, guess2, price, r)
{
  var best;
  if guess1 <= price && guess2 <= price
  {
    if guess1 > guess2
    {
      best := guess1;
    }
    else
    {
      best := guess2;
    }
    return best;
  }
  if guess1 > price && guess2 <= price
  {
    best := guess2;
    return best;
  }
  if guess1 <= price && guess2 > price
  {
    best := guess1;
    return best;
  }
  
  best:= -1;
  return best;
}

