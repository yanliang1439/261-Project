const MIN: int := 1
const MAX: int := 100

type GuessHistory = seq<int>

method ValidateGuess(guess: int)
  requires MIN <= guess <= MAX
{
}

method CheckWin(guess: int, target: int) returns (won: bool)
  requires MIN <= guess <= MAX
  requires MIN <= target <= MAX
  ensures won <==> guess == target
{
  won := guess == target;
}

method GenerateGuess(history: GuessHistory, lo: int, hi: int) returns (guess: int)
  requires lo <= hi
  ensures lo <= guess <= hi
{
  guess := lo + (hi - lo) / 2;
}

method PlayGuess(target: int, max_attempts: int) returns (won: bool)
  requires MIN <= target <= MAX
  requires max_attempts > 0
  ensures won ==> 0 < max_attempts
  ensures !won ==> max_attempts >= 0
{
  var attempts := 0;
  var guess := MIN;
  var history: GuessHistory := [];

  while guess != target && attempts < max_attempts
    invariant 0 <= attempts <= max_attempts
    invariant MIN <= target <= MAX
    invariant forall g :: g in history ==> MIN <= g <= MAX
  {
    guess := GenerateGuess(history, MIN, MAX);
    history := history + [guess];
    attempts := attempts + 1;
  }

  won := guess == target;
}
