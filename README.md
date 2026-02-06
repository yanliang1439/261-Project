# Verified Guess Number Game with AI

This project implements a CLI Guess Number game with AI player. 
The main focus is **verification using Dafny**:
- Loop invariants
- Precondition and postcondition checks
- AI correctness

## How to run

1. Install Dafny: https://dafny.org
2. Open terminal and navigate to src/
3. Run: `dafny GuessNumber.dfy /compile:3 /verify:3`

## Project structure

- `src/`: Dafny source files
- `docs/`: Verification explanation and screenshots
- `PPT/`: Presentation slides
