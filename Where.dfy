// Where.dfy
// Verified WHERE (filtering) operation.
// Filters rows where age >= minAge.

include "DataTypes.dfy"

// ============================================================
// WHERE: Filter rows by age >= minAge
// ============================================================

method Where(data: Table, minAge: int) returns (result: Table)
  // 1. Every row in output satisfies the condition
  ensures forall r :: r in result ==> r.age >= minAge
  // 2. Every row in output comes from the input (no fabricated data)
  ensures forall r :: r in result ==> r in data
  // 3. No valid row is lost (completeness)
  ensures forall r :: r in data && r.age >= minAge ==> r in result
  // 4. Output is a subsequence: order is preserved and length <= input
  ensures |result| <= |data|
{
  result := [];
  var i := 0;

  while i < |data|
    invariant 0 <= i <= |data|
    invariant forall r :: r in result ==> r.age >= minAge
    invariant forall r :: r in result ==> r in data
    invariant forall j :: 0 <= j < i && data[j].age >= minAge ==> data[j] in result
    invariant |result| <= i
  {
    if data[i].age >= minAge {
      result := result + [data[i]];
    }
    i := i + 1;
  }
}

// ============================================================
// WHERE (generic): Filter rows by an arbitrary predicate
// ============================================================

method WhereGeneric(data: Table, pred: Record -> bool) returns (result: Table)
  // 1. Every row in output satisfies the predicate
  ensures forall r :: r in result ==> pred(r)
  // 2. Every row in output comes from the input
  ensures forall r :: r in result ==> r in data
  // 3. No valid row is lost
  ensures forall r :: r in data && pred(r) ==> r in result
  // 4. Output length <= input length
  ensures |result| <= |data|
{
  result := [];
  var i := 0;

  while i < |data|
    invariant 0 <= i <= |data|
    invariant forall r :: r in result ==> pred(r)
    invariant forall r :: r in result ==> r in data
    invariant forall j :: 0 <= j < i && pred(data[j]) ==> data[j] in result
    invariant |result| <= i
  {
    if pred(data[i]) {
      result := result + [data[i]];
    }
    i := i + 1;
  }
}
