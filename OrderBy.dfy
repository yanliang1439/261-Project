// OrderBy.dfy
// Verified ORDER BY (sorting) operation.
// Sorts rows by salary in non-decreasing order using insertion sort.
// Proves: (1) output is sorted, (2) output is a permutation of input.

include "DataTypes.dfy"

// ============================================================
// Helper: Insert a record into an already-sorted sequence
// at the correct position (by salary).
// ============================================================

method InsertSorted(sorted: Table, rec: Record) returns (result: Table)
  requires SortedBySalary(sorted)
  // 1. Output is still sorted
  ensures SortedBySalary(result)
  // 2. Output is a permutation of sorted + [rec]
  ensures multiset(result) == multiset(sorted) + multiset{rec}
  // 3. Length increases by 1
  ensures |result| == |sorted| + 1
{
  // Find the insertion point
  var i := |sorted|;

  while i > 0 && sorted[i - 1].salary > rec.salary
    invariant 0 <= i <= |sorted|
    invariant forall j :: i <= j < |sorted| ==> sorted[j].salary >= rec.salary
  {
    i := i - 1;
  }

  // Insert at position i
  result := sorted[..i] + [rec] + sorted[i..];

  // Help Dafny verify the multiset property
  assert sorted == sorted[..i] + sorted[i..];

  // Help Dafny verify sorted property
  assert forall j :: 0 <= j < i ==> sorted[j].salary <= rec.salary
    by {
      if i > 0 {
        // All elements before i have salary <= rec.salary
        // because we stopped the while loop
        assert forall j :: 0 <= j < i ==>
          sorted[j].salary <= sorted[i - 1].salary <= rec.salary
          by {
            // sorted is sorted, so elements before i are <= sorted[i-1]
          }
      }
    }
}

// ============================================================
// ORDER BY salary (ascending) using insertion sort
// ============================================================

method OrderBySalary(data: Table) returns (result: Table)
  // 1. Output is sorted by salary in non-decreasing order
  ensures SortedBySalary(result)
  // 2. Output is a permutation of input (no data lost or added)
  ensures multiset(result) == multiset(data)
  // 3. Same number of rows
  ensures |result| == |data|
{
  result := [];
  var i := 0;

  while i < |data|
    invariant 0 <= i <= |data|
    invariant SortedBySalary(result)
    invariant |result| == i
    invariant multiset(result) == multiset(data[..i])
  {
    result := InsertSorted(result, data[i]);

    // Help Dafny see that data[..i] + [data[i]] == data[..i+1]
    assert data[..i] + [data[i]] == data[..i + 1];

    i := i + 1;
  }

  // Help Dafny see that data[..|data|] == data
  assert data[..|data|] == data;
}

// ============================================================
// ORDER BY salary (descending)
// ============================================================

predicate SortedBySalaryDesc(data: Table)
{
  forall i, j :: 0 <= i < j < |data| ==> data[i].salary >= data[j].salary
}

method OrderBySalaryDesc(data: Table) returns (result: Table)
  // 1. Output is sorted by salary in non-increasing order
  ensures SortedBySalaryDesc(result)
  // 2. Output is a permutation of input
  ensures multiset(result) == multiset(data)
  // 3. Same number of rows
  ensures |result| == |data|
{
  // First sort ascending, then reverse
  var ascending := OrderBySalary(data);
  result := Reverse(ascending);

  // multiset is preserved by reverse
  ReversePreservesMultiset(ascending);
}

// ============================================================
// Helper: Reverse a sequence
// ============================================================

method Reverse(data: Table) returns (result: Table)
  ensures |result| == |data|
  ensures forall i :: 0 <= i < |data| ==> result[i] == data[|data| - 1 - i]
  ensures multiset(result) == multiset(data)
{
  result := [];
  var i := |data|;

  while i > 0
    invariant 0 <= i <= |data|
    invariant |result| == |data| - i
    invariant forall j :: 0 <= j < |data| - i ==> result[j] == data[|data| - 1 - j]
    invariant multiset(result) == multiset(data[i..])
  {
    i := i - 1;
    result := result + [data[i]];
    assert data[i..] == [data[i]] + data[i + 1..];
  }

  assert data[0..] == data;
}

// ============================================================
// Lemma: Reversing preserves multiset
// ============================================================

lemma ReversePreservesMultiset(data: Table)
  ensures multiset(data) == multiset(data)
{
  // Trivially true; the multiset proof is handled in the Reverse method.
}
