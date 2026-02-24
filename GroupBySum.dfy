// GroupBySum.dfy
// Verified GROUP BY + SUM aggregation operation.
// Groups rows by dept and computes the sum of salary for each group.

include "DataTypes.dfy"

// ============================================================
// Result type for aggregation
// ============================================================

datatype AggResult = AggResult(dept: int, totalSalary: int)

// ============================================================
// Helper: Collect all distinct dept values into a sequence
// ============================================================

method CollectDistinctDepts(data: Table) returns (depts: seq<int>)
  // 1. No duplicates in the output
  ensures forall i, j :: 0 <= i < j < |depts| ==> depts[i] != depts[j]
  // 2. Every dept in data appears in output
  ensures forall k :: 0 <= k < |data| ==> data[k].dept in depts
  // 3. Every dept in output actually exists in data
  ensures forall d :: d in depts ==> exists k :: 0 <= k < |data| && data[k].dept == d
{
  depts := [];
  var i := 0;

  while i < |data|
    invariant 0 <= i <= |data|
    invariant forall a, b :: 0 <= a < b < |depts| ==> depts[a] != depts[b]
    invariant forall k :: 0 <= k < i ==> data[k].dept in depts
    invariant forall d :: d in depts ==> exists k :: 0 <= k < i && data[k].dept == d
  {
    if data[i].dept !in depts {
      depts := depts + [data[i].dept];
    }
    i := i + 1;
  }
}

// ============================================================
// Helper: Compute the sum of salary for rows matching a given dept
// ============================================================

method ComputeDeptSum(data: Table, dept: int) returns (total: int)
  // The result equals the recursive definition SumSalaryOfDept
  ensures total == SumSalaryOfDept(data, dept)
{
  total := 0;
  var i := 0;

  while i < |data|
    invariant 0 <= i <= |data|
    invariant total == SumSalaryOfDept(data[..i], dept)
  {
    if data[i].dept == dept {
      total := total + data[i].salary;
    }

    // Help Dafny connect data[..i+1] with data[..i] and data[i]
    SumSalaryLemma(data, i, dept);

    i := i + 1;
  }

  // Help Dafny see that data[..|data|] == data
  assert data[..|data|] == data;
}

// ============================================================
// Lemma: Connects SumSalaryOfDept(data[..i+1]) with data[..i] and data[i]
// ============================================================

lemma SumSalaryLemma(data: Table, i: int, dept: int)
  requires 0 <= i < |data|
  ensures data[..i + 1] == data[..i] + [data[i]]
  ensures SumSalaryOfDept(data[..i + 1], dept) ==
    (if data[i].dept == dept
     then SumSalaryOfDept(data[..i], dept) + data[i].salary
     else SumSalaryOfDept(data[..i], dept))
{
  var prefix := data[..i + 1];
  assert prefix == data[..i] + [data[i]];
  SumSalaryAppendLemma(data[..i], data[i], dept);
}

// ============================================================
// Lemma: SumSalaryOfDept for appending a single element
// ============================================================

lemma SumSalaryAppendLemma(s: Table, r: Record, dept: int)
  ensures SumSalaryOfDept(s + [r], dept) ==
    (if r.dept == dept
     then SumSalaryOfDept(s, dept) + r.salary
     else SumSalaryOfDept(s, dept))
{
  if |s| == 0 {
    assert s + [r] == [r];
  } else {
    assert (s + [r])[0] == s[0];
    assert (s + [r])[1..] == s[1..] + [r];
    SumSalaryAppendLemma(s[1..], r, dept);
  }
}

// ============================================================
// GROUP BY dept, SUM(salary)
// ============================================================

method GroupBySum(data: Table) returns (result: seq<AggResult>)
  // 1. Every dept in data appears in the result
  ensures forall k :: 0 <= k < |data| ==>
    exists j :: 0 <= j < |result| && result[j].dept == data[k].dept
  // 2. No duplicate depts in the result
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i].dept != result[j].dept
  // 3. Each totalSalary equals the true sum for that dept
  ensures forall j :: 0 <= j < |result| ==>
    result[j].totalSalary == SumSalaryOfDept(data, result[j].dept)
  // 4. Every dept in result actually exists in data
  ensures forall j :: 0 <= j < |result| ==>
    exists k :: 0 <= k < |data| && data[k].dept == result[j].dept
{
  // Step 1: Collect distinct depts
  var depts := CollectDistinctDepts(data);

  // Step 2: For each dept, compute the sum
  result := [];
  var i := 0;

  while i < |depts|
    invariant 0 <= i <= |depts|
    invariant |result| == i
    // Each result entry corresponds to depts[j]
    invariant forall j :: 0 <= j < i ==> result[j].dept == depts[j]
    // Each result entry has the correct sum
    invariant forall j :: 0 <= j < i ==>
      result[j].totalSalary == SumSalaryOfDept(data, result[j].dept)
    // No duplicate depts (inherited from depts being distinct)
    invariant forall a, b :: 0 <= a < b < i ==> result[a].dept != result[b].dept
    // Every dept in result exists in data
    invariant forall j :: 0 <= j < i ==>
      exists k :: 0 <= k < |data| && data[k].dept == result[j].dept
  {
    assert depts[i] in depts;
    var total := ComputeDeptSum(data, depts[i]);
    result := result + [AggResult(depts[i], total)];
    i := i + 1;
  }

  // Prove postcondition 1: every dept in data appears in result
  assert forall k :: 0 <= k < |data| ==> data[k].dept in depts;
  assert |result| == |depts|;
  assert forall j :: 0 <= j < |result| ==> result[j].dept == depts[j];

  forall k | 0 <= k < |data|
    ensures exists j :: 0 <= j < |result| && result[j].dept == data[k].dept
  {
    assert data[k].dept in depts;
    var idx :| 0 <= idx < |depts| && depts[idx] == data[k].dept;
    assert result[idx].dept == depts[idx] == data[k].dept;
  }
}
