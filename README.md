# SAT Solver (DPLL-Based with Heuristics)

## Overview

This project implements a Boolean Satisfiability (SAT) solver using the **Davis–Putnam–Logemann–Loveland (DPLL)** algorithm, enhanced with several practical heuristics.

The solver determines whether a Boolean formula in **Conjunctive Normal Form (CNF)** is satisfiable and outputs either:

- `RESULT:SAT` with a satisfying assignment  
- `RESULT:UNSAT`

The solver supports input in **DIMACS CNF format**, including `.cnf` and `.cnf.Z` files.

---

## Features

- DPLL recursive backtracking algorithm
- Boolean Constraint Propagation (BCP)
- Watched literals optimization
- DLIS decision heuristic
- Non-chronological backtracking (backjumping)

---

## How It Works

### High-Level Algorithm

The solver follows this process:

1. Parse the CNF input (DIMACS format)
2. Apply initial unit clause assignments
3. Repeat:
   - Select a variable using the DLIS heuristic
   - Assign a value (True/False)
   - Propagate implications using BCP
   - If a conflict occurs:
     - Perform backtracking (possibly non-chronological)
4. If all variables are assigned without conflict → SAT
5. If all branches fail → UNSAT

---

## Core Components

### 1. DPLL (Baseline Algorithm)

The solver uses recursive backtracking to explore possible assignments.

Key operations:
- Variable selection
- Assignment
- Conflict detection
- Backtracking

Implemented primarily in:
- `_search()`
- `assign_literal()`
- `backtrack_to_level()`

---

### 2. Boolean Constraint Propagation (BCP)

BCP simplifies the formula by propagating forced assignments from unit clauses.

- Detects unit clauses
- Assigns implied values
- Detects conflicts early

Implemented in:
- `propagate()`

---

### 3. Watched Literals

Each clause tracks two "watched literals" to avoid scanning all clauses during propagation.

Benefits:
- Efficient propagation
- Reduced runtime
- Scales better for large formulas

Data structures:
- `watch_list`
- `watched_pos`

---

### 4. DLIS Heuristic

The **Dynamic Largest Individual Sum (DLIS)** heuristic selects the next variable.

Strategy:
- Count occurrences of literals in unsatisfied clauses
- Choose the most frequent literal

Effect:
- Reduces search depth
- Improves solver performance

Implemented in:
- `choose_literal_dlis()`

---

### 5. Non-Chronological Backtracking

Instead of backtracking one level at a time, the solver jumps back multiple levels when a conflict occurs.

Steps:
1. Identify variables involved in the conflict
2. Compute relevant decision levels
3. Jump back to the second-highest level

Benefits:
- Avoids redundant exploration
- Improves efficiency over naive backtracking

Implemented in:
- `compute_backjump_level()`
- `conflict_var_set()`

---

## Limitations

This solver is a **simplified SAT solver** and does not include:

- Conflict-Driven Clause Learning (CDCL)
- VSIDS heuristic
- Restart strategies

However, it captures the key ideas behind modern SAT solvers and demonstrates the impact of heuristics on performance.

---

## Usage

### Run the solver

```bash
python3 SAT1.py input.cnf