// Select.dfy
// Verified SELECT (projection) operation.
// Projects specific fields from each record.

include "DataTypes.dfy"

// ============================================================
// Since Dafny is statically typed, we define projected record types.
// Each "Select" variant returns a different subset of columns.
// ============================================================

// Projected record: only id and salary
datatype RecordIdSalary = RecordIdSalary(id: int, salary: int)

// Projected record: only id and age
datatype RecordIdAge = RecordIdAge(id: int, age: int)

// Projected record: only id and dept
datatype RecordIdDept = RecordIdDept(id: int, dept: int)

// ============================================================
// SELECT id, salary FROM table
// ============================================================

method SelectIdSalary(data: Table) returns (result: seq<RecordIdSalary>)
  // 1. Row count is preserved
  ensures |result| == |data|
  // 2. Each projected row corresponds to the original row
  ensures forall i :: 0 <= i < |data| ==>
    result[i].id == data[i].id && result[i].salary == data[i].salary
{
  result := [];
  var i := 0;

  while i < |data|
    invariant 0 <= i <= |data|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      result[j].id == data[j].id && result[j].salary == data[j].salary
  {
    result := result + [RecordIdSalary(data[i].id, data[i].salary)];
    i := i + 1;
  }
}

// ============================================================
// SELECT id, age FROM table
// ============================================================

method SelectIdAge(data: Table) returns (result: seq<RecordIdAge>)
  // 1. Row count is preserved
  ensures |result| == |data|
  // 2. Each projected row corresponds to the original row
  ensures forall i :: 0 <= i < |data| ==>
    result[i].id == data[i].id && result[i].age == data[i].age
{
  result := [];
  var i := 0;

  while i < |data|
    invariant 0 <= i <= |data|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      result[j].id == data[j].id && result[j].age == data[j].age
  {
    result := result + [RecordIdAge(data[i].id, data[i].age)];
    i := i + 1;
  }
}

// ============================================================
// SELECT id, dept FROM table
// ============================================================

method SelectIdDept(data: Table) returns (result: seq<RecordIdDept>)
  // 1. Row count is preserved
  ensures |result| == |data|
  // 2. Each projected row corresponds to the original row
  ensures forall i :: 0 <= i < |data| ==>
    result[i].id == data[i].id && result[i].dept == data[i].dept
{
  result := [];
  var i := 0;

  while i < |data|
    invariant 0 <= i <= |data|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      result[j].id == data[j].id && result[j].dept == data[j].dept
  {
    result := result + [RecordIdDept(data[i].id, data[i].dept)];
    i := i + 1;
  }
}
