# Verified SQL Query Engine in Dafny

A formally verified implementation of core SQL operations in [Dafny](https://dafny.org/). Each operation is proven correct using preconditions, postconditions, and loop invariants — guaranteeing no data loss, no fabricated results, and correct computation.

## Project Structure

| File | SQL Operation | Description |
|------|--------------|-------------|
| `DataTypes.dfy` | — | Core data types (`Record`, `Table`) and helper predicates |
| `Where.dfy` | `WHERE` | Filters rows by condition (e.g., `age >= 18`) |
| `Select.dfy` | `SELECT` | Projects specific columns (e.g., `id, salary`) |
| `OrderBy.dfy` | `ORDER BY` | Sorts rows by salary (ascending/descending) via insertion sort |
| `GroupBySum.dfy` | `GROUP BY ... SUM()` | Groups by department and computes salary totals |
| `Main.dfy` | — | Demo program executing all queries on sample employee data |
| `go` | — | Build & verify script |

## Verified Properties

### WHERE (Filtering)
- All output rows satisfy the filter condition
- No qualifying rows are lost
- Output order matches input order

### SELECT (Projection)
- Row count is preserved
- Each output row corresponds to the correct input row

### ORDER BY (Sorting)
- Output is sorted in the specified order
- Output is a permutation of the input (multiset equality)
- Row count is preserved

### GROUP BY + SUM (Aggregation)
- Every department in the input appears in the result
- No duplicate departments in the output
- Each department's salary sum is correct
- No phantom departments are introduced

## Data Model

```dafny
datatype Record = Record(id: int, age: int, salary: int, dept: int)
type Table = seq<Record>
```

Sample employee table used in `Main.dfy`:

| id | age | salary | dept |
|----|-----|--------|------|
| 1  | 30  | 50000  | 1    |
| 2  | 17  | 30000  | 2    |
| 3  | 25  | 60000  | 1    |
| 4  | 40  | 80000  | 3    |
| 5  | 16  | 25000  | 2    |
| 6  | 35  | 70000  | 3    |

## How to Run

Make sure [Dafny](https://github.com/dafny-lang/dafny) is installed, then:

```bash
# Verify all modules
dafny verify DataTypes.dfy
dafny verify Where.dfy
dafny verify Select.dfy
dafny verify OrderBy.dfy
dafny verify GroupBySum.dfy

# Run the demo
dafny run Main.dfy
```

Or simply run the provided script:

```bash
bash go
```
