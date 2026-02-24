// Main.dfy
// Demonstration of the Verified SQL Query Engine.
// Runs example queries on sample data and prints results.

include "DataTypes.dfy"
include "Where.dfy"
include "Select.dfy"
include "OrderBy.dfy"
include "GroupBySum.dfy"

// ============================================================
// Helper: Print a table
// ============================================================

method PrintTable(data: Table)
{
  var i := 0;
  print "  id  | age | salary | dept\n";
  print "  ----+-----+--------+-----\n";
  while i < |data|
    invariant 0 <= i <= |data|
  {
    print "  ", data[i].id, "   | ", data[i].age, "  | ", data[i].salary, "    | ", data[i].dept, "\n";
    i := i + 1;
  }
  print "\n";
}

// ============================================================
// Helper: Print aggregation results
// ============================================================

method PrintAggResults(results: seq<AggResult>)
{
  var i := 0;
  print "  dept | total_salary\n";
  print "  -----+-------------\n";
  while i < |results|
    invariant 0 <= i <= |results|
  {
    print "  ", results[i].dept, "    | ", results[i].totalSalary, "\n";
    i := i + 1;
  }
  print "\n";
}

// ============================================================
// Helper: Print projected results (id, salary)
// ============================================================

method PrintIdSalary(results: seq<RecordIdSalary>)
{
  var i := 0;
  print "  id  | salary\n";
  print "  ----+-------\n";
  while i < |results|
    invariant 0 <= i <= |results|
  {
    print "  ", results[i].id, "   | ", results[i].salary, "\n";
    i := i + 1;
  }
  print "\n";
}

// ============================================================
// Main method: run all example queries
// ============================================================

method Main()
{
  // ---- Sample Data ----
  // Represents an employee table:
  //   id=1, Alice,  age=25, salary=5000, dept=1 (IT)
  //   id=2, Bob,    age=16, salary=3000, dept=2 (HR)
  //   id=3, Carol,  age=30, salary=7000, dept=1 (IT)
  //   id=4, Dave,   age=22, salary=4500, dept=2 (HR)
  //   id=5, Eve,    age=45, salary=9000, dept=3 (Finance)
  //   id=6, Frank,  age=15, salary=2000, dept=3 (Finance)

  var data: Table := [
    Record(1, 25, 5000, 1),
    Record(2, 16, 3000, 2),
    Record(3, 30, 7000, 1),
    Record(4, 22, 4500, 2),
    Record(5, 45, 9000, 3),
    Record(6, 15, 2000, 3)
  ];

  print "========================================\n";
  print "  Verified SQL Query Engine - Demo\n";
  print "========================================\n\n";

  // ---- Original Table ----
  print ">> Original Table:\n";
  PrintTable(data);

  // ---- Query 1: WHERE age >= 18 ----
  print ">> Query 1: WHERE age >= 18\n";
  var filtered := Where(data, 18);
  PrintTable(filtered);

  // ---- Query 2: SELECT id, salary ----
  print ">> Query 2: SELECT id, salary FROM table\n";
  var projected := SelectIdSalary(data);
  PrintIdSalary(projected);

  // ---- Query 3: ORDER BY salary ASC ----
  print ">> Query 3: ORDER BY salary ASC\n";
  var sorted := OrderBySalary(data);
  PrintTable(sorted);

  // ---- Query 4: ORDER BY salary DESC ----
  print ">> Query 4: ORDER BY salary DESC\n";
  var sortedDesc := OrderBySalaryDesc(data);
  PrintTable(sortedDesc);

  // ---- Query 5: GROUP BY dept, SUM(salary) ----
  print ">> Query 5: GROUP BY dept, SUM(salary)\n";
  var grouped := GroupBySum(data);
  PrintAggResults(grouped);

  // ---- Combined Query: WHERE age >= 18, then ORDER BY salary ----
  print ">> Query 6: WHERE age >= 18 ORDER BY salary ASC\n";
  var step1 := Where(data, 18);
  var step2 := OrderBySalary(step1);
  PrintTable(step2);

  print "========================================\n";
  print "  All queries verified by Dafny!\n";
  print "========================================\n";
}
