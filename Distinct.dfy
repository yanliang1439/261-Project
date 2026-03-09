// Distinct.dfy
// Verified DISTINCT operation.
// Removes duplicate rows from a table, preserving order of first occurrence.

include "DataTypes.dfy"

// ============================================================
// DISTINCT: Remove duplicate rows
// Equivalent to SELECT DISTINCT * FROM table
// ============================================================

method Distinct(data: Table) returns (result: Table)
  // 1. No duplicates in the output
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
  // 2. Every row in the output comes from the input
  ensures forall r :: r in result ==> r in data
  // 3. Every row in the input appears in the output
  ensures forall r :: r in data ==> r in result
  // 4. Output size <= input size
  ensures |result| <= |data|
{
  result := [];
  var i := 0;

  while i < |data|
    invariant 0 <= i <= |data|
    invariant forall a, b :: 0 <= a < b < |result| ==> result[a] != result[b]
    invariant forall r :: r in result ==> r in data
    invariant forall k :: 0 <= k < i ==> data[k] in result
    invariant |result| <= i
  {
    if data[i] !in result {
      result := result + [data[i]];
    }
    i := i + 1;
  }
}

// ============================================================
// DISTINCT with set semantics verification:
// Additionally proves that the output and input contain the
// same set of records (set equivalence).
// ============================================================

method DistinctWithSetEquiv(data: Table) returns (result: Table)
  // 1. No duplicates in the output
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
  // 2. Set equivalence: output contains exactly the same records as input
  ensures forall r :: r in result <==> r in data
  // 3. Output size <= input size
  ensures |result| <= |data|
  // 4. Output is a subset of input as a multiset
  //    (every record appears at most as many times as in input)
  ensures forall r :: r in result ==> multiset(result)[r] <= multiset(data)[r]
{
  result := [];
  var i := 0;

  while i < |data|
    invariant 0 <= i <= |data|
    invariant forall a, b :: 0 <= a < b < |result| ==> result[a] != result[b]
    invariant forall r :: r in result ==> r in data
    invariant forall k :: 0 <= k < i ==> data[k] in result
    invariant |result| <= i
    invariant forall r :: r in result ==> multiset(result)[r] == 1
  {
    if data[i] !in result {
      result := result + [data[i]];
    }
    i := i + 1;
  }

  // Each record appears exactly once in result, but possibly
  // multiple times in data, so multiset(result)[r] <= multiset(data)[r]
  forall r | r in result
    ensures multiset(result)[r] <= multiset(data)[r]
  {
    assert multiset(result)[r] == 1;
    assert r in data;
  }
}
