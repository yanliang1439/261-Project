// DataTypes.dfy
// Core data types and helper functions for the Verified SQL Query Engine.

// A single record (row) in our table.
// For simplicity, all fields are integers.
datatype Record = Record(id: int, age: int, salary: int, dept: int)

// A table is simply a sequence of records.
type Table = seq<Record>

// ============================================================
// Validity Predicates
// ============================================================

// A record is valid if all fields are non-negative.
predicate ValidRecord(r: Record)
{
  r.id >= 0 && r.age >= 0 && r.salary >= 0 && r.dept >= 0
}

// Every record in the table is valid.
predicate AllValid(data: Table)
{
  forall i :: 0 <= i < |data| ==> ValidRecord(data[i])
}

// ============================================================
// Helper: Check if a value exists in a sequence of integers
// ============================================================

predicate InSeq(x: int, s: seq<int>)
{
  exists i :: 0 <= i < |s| && s[i] == x
}

// ============================================================
// Helper: Collect all distinct dept values from a table
// ============================================================

function DistinctDepts(data: Table): set<int>
{
  set i | 0 <= i < |data| :: data[i].dept
}

// ============================================================
// Helper: Sum of salary for a specific dept in a table
// ============================================================

function SumSalaryOfDept(data: Table, dept: int): int
{
  if |data| == 0 then 0
  else if data[0].dept == dept then
    data[0].salary + SumSalaryOfDept(data[1..], dept)
  else
    SumSalaryOfDept(data[1..], dept)
}

// ============================================================
// Helper: Check if a sequence is sorted by salary (non-decreasing)
// ============================================================

predicate SortedBySalary(data: Table)
{
  forall i, j :: 0 <= i < j < |data| ==> data[i].salary <= data[j].salary
}
