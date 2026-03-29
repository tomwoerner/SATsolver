#!/usr/bin/env python3
"""
SAT1.py

A SAT solver for DIMACS CNF using:
- DPLL
- Boolean Constraint Propagation (BCP)
- Watched literals
- DLIS-style decision heuristic
- Simple non-chronological backtracking (backjumping)

Usage:
    python3 SAT1.py benchmark.cnf

Output format:
    RESULT:SAT
    ASSIGNMENT:1=1 2=0 3=1 ...
or
    RESULT:UNSAT
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple
import subprocess
import tempfile
from pathlib import Path

@dataclass
class CNFFormula:
    num_vars: int
    clauses: List[List[int]]

def lit_var(lit: int) -> int:
    return abs(lit)

def lit_sign_value(lit: int) -> int:
    return 1 if lit > 0 else 0

def negate(lit: int) -> int:
    return -lit

def open_cnf_file(path: Path):
    import subprocess
    import tempfile
    import shutil

    if path.suffix.lower() != ".z":
        return path.open("r", encoding="utf-8", errors="replace")

    tmp = tempfile.NamedTemporaryFile(delete=False, suffix=".cnf")
    tmp_path = Path(tmp.name)
    tmp.close()

    def try_command(cmd):
        try:
            with open(tmp_path, "wb") as out:
                result = subprocess.run(
                    cmd,
                    stdout=out,
                    stderr=subprocess.PIPE,
                    shell=True  # <-- IMPORTANT for Windows
                )
            return result.returncode == 0
        except Exception:
            return False

    # Try different tools
    if try_command(f'gzip -d -c "{path}"'):
        return tmp_path.open("r", encoding="utf-8", errors="replace")

    if try_command(f'uncompress -c "{path}"'):
        return tmp_path.open("r", encoding="utf-8", errors="replace")

    # 🔥 FORCE full path to 7z (this is the fix)
    seven_zip = shutil.which("7z") or r"C:\Program Files\7-Zip\7z.exe"

    if try_command(f'"{seven_zip}" e -so "{path}"'):
        return tmp_path.open("r", encoding="utf-8", errors="replace")

    raise RuntimeError(
        f"Cannot decompress .Z file.\nTried gzip, uncompress, and 7z.\n"
        f"Make sure 7z is installed at: {seven_zip}"
    )


def parse_dimacs_cnf(path: str | Path):
    path = Path(path)

    num_vars = None
    expected_num_clauses = None
    clauses = []
    current_clause = []

    with open_cnf_file(path) as f:
        for line_no, raw_line in enumerate(f, start=1):
            line = raw_line.strip()

            if not line or line.startswith("c"):
                continue

            if line.startswith("p"):
                parts = line.split()
                if len(parts) != 4 or parts[1] != "cnf":
                    raise ValueError(f"Invalid problem line at line {line_no}: {line}")
                num_vars = int(parts[2])
                expected_num_clauses = int(parts[3])
                continue

            if num_vars is None:
                raise ValueError("Clause data before problem line")

            for token in line.split():
                lit = int(token)
                if lit == 0:
                    clauses.append(current_clause)
                    current_clause = []
                else:
                    current_clause.append(lit)

    if current_clause:
        raise ValueError("Last clause missing terminating 0")

    if len(clauses) != expected_num_clauses:
        raise ValueError("Clause count mismatch")

    return CNFFormula(num_vars=num_vars, clauses=clauses)


class SATSolver:
    def __init__(self, formula: CNFFormula):
        self.n = formula.num_vars
        self.clauses: List[List[int]] = formula.clauses

        self.assignment: List[int] = [-1] * (self.n + 1)  # -1 unassigned, 0 false, 1 true
        self.level_of_var: List[int] = [-1] * (self.n + 1)
        self.reason_of_var: List[Optional[int]] = [None] * (self.n + 1)

        self.trail: List[Tuple[int, int, int, Optional[int]]] = []
        self.trail_limits: List[int] = [0]
        self.current_level = 0
        self.prop_q = 0

        self.watch_list: Dict[int, List[int]] = {}
        self.watched_pos: List[List[int]] = []

        self.decisions = 0
        self.propagations = 0
        self.conflicts = 0
        self.backjumps = 0

        self._init_watch_structures()

    def _init_watch_structures(self) -> None:
        for ci, clause in enumerate(self.clauses):
            if len(clause) == 0:
                self.watched_pos.append([])
            elif len(clause) == 1:
                self.watched_pos.append([0, 0])
                self.watch_list.setdefault(clause[0], []).append(ci)
            else:
                self.watched_pos.append([0, 1])
                self.watch_list.setdefault(clause[0], []).append(ci)
                self.watch_list.setdefault(clause[1], []).append(ci)

    def value_of_literal(self, lit: int) -> Optional[bool]:
        val = self.assignment[abs(lit)]
        if val == -1:
            return None
        return (val == 1) if lit > 0 else (val == 0)

    def is_clause_satisfied(self, clause: List[int]) -> bool:
        return any(self.value_of_literal(lit) is True for lit in clause)

    def assign_literal(self, lit: int, level: int, reason_clause: Optional[int]) -> bool:
        var = abs(lit)
        value = 1 if lit > 0 else 0
        current = self.assignment[var]

        if current == -1:
            self.assignment[var] = value
            self.level_of_var[var] = level
            self.reason_of_var[var] = reason_clause
            self.trail.append((var, value, level, reason_clause))
            return True

        return current == value

    def enqueue_unit_clause(self, ci: int, lit: int) -> Optional[int]:
        if not self.assign_literal(lit, self.current_level, ci):
            return ci
        return None

    def propagate(self) -> Optional[int]:
        while self.prop_q < len(self.trail):
            var, value, _level, _reason = self.trail[self.prop_q]
            self.prop_q += 1
            self.propagations += 1

            true_lit = var if value == 1 else -var
            false_lit = -true_lit

            watched_clauses = list(self.watch_list.get(false_lit, []))
            for ci in watched_clauses:
                clause = self.clauses[ci]

                if len(clause) == 0:
                    self.conflicts += 1
                    return ci

                if len(clause) == 1:
                    only_lit = clause[0]
                    v = self.value_of_literal(only_lit)
                    if v is False:
                        self.conflicts += 1
                        return ci
                    if v is None:
                        c = self.enqueue_unit_clause(ci, only_lit)
                        if c is not None:
                            self.conflicts += 1
                            return c
                    continue

                wp0, wp1 = self.watched_pos[ci]
                if clause[wp0] == false_lit:
                    false_watch_idx, other_watch_idx = 0, 1
                elif clause[wp1] == false_lit:
                    false_watch_idx, other_watch_idx = 1, 0
                else:
                    continue

                fw_pos = self.watched_pos[ci][false_watch_idx]
                ow_pos = self.watched_pos[ci][other_watch_idx]
                other_lit = clause[ow_pos]
                other_val = self.value_of_literal(other_lit)

                if other_val is True:
                    continue

                moved = False
                for new_pos, candidate in enumerate(clause):
                    if new_pos == fw_pos or new_pos == ow_pos:
                        continue
                    cand_val = self.value_of_literal(candidate)
                    if cand_val is not False:
                        self.watch_list[false_lit].remove(ci)
                        self.watch_list.setdefault(candidate, []).append(ci)
                        self.watched_pos[ci][false_watch_idx] = new_pos
                        moved = True
                        break

                if moved:
                    continue

                if other_val is False:
                    self.conflicts += 1
                    return ci

                c = self.enqueue_unit_clause(ci, other_lit)
                if c is not None:
                    self.conflicts += 1
                    return c

        return None

    def choose_literal_dlis(self) -> Optional[int]:
        scores: Dict[int, int] = {}
        for clause in self.clauses:
            if self.is_clause_satisfied(clause):
                continue
            for lit in clause:
                var = abs(lit)
                if self.assignment[var] == -1:
                    scores[lit] = scores.get(lit, 0) + 1
        if not scores:
            return None
        return max(scores.items(), key=lambda kv: kv[1])[0]

    def all_assigned(self) -> bool:
        return all(self.assignment[var] != -1 for var in range(1, self.n + 1))

    def conflict_var_set(self, conflict_clause_idx: int) -> Set[int]:
        visited: Set[int] = set()
        stack: List[int] = [abs(lit) for lit in self.clauses[conflict_clause_idx]]

        while stack:
            var = stack.pop()
            if var in visited:
                continue
            visited.add(var)
            reason = self.reason_of_var[var]
            if reason is not None:
                for lit in self.clauses[reason]:
                    parent = abs(lit)
                    if parent not in visited:
                        stack.append(parent)
        return visited

    def compute_backjump_level(self, conflict_clause_idx: int) -> int:
        vars_in_conflict = self.conflict_var_set(conflict_clause_idx)
        levels = sorted(
            {self.level_of_var[v] for v in vars_in_conflict if self.level_of_var[v] >= 0},
            reverse=True,
        )
        if not levels:
            return 0
        if len(levels) == 1:
            return 0
        return levels[1]

    def backtrack_to_level(self, target_level: int) -> None:
        while self.current_level > target_level:
            start = self.trail_limits.pop()
            for i in range(len(self.trail) - 1, start - 1, -1):
                var, _value, _level, _reason = self.trail.pop()
                self.assignment[var] = -1
                self.level_of_var[var] = -1
                self.reason_of_var[var] = None
            self.current_level -= 1
        self.prop_q = min(self.prop_q, len(self.trail))

    def solve(self) -> bool:
        for clause in self.clauses:
            if len(clause) == 0:
                return False

        for ci, clause in enumerate(self.clauses):
            if len(clause) == 1:
                c = self.enqueue_unit_clause(ci, clause[0])
                if c is not None:
                    return False

        c = self.propagate()
        if c is not None:
            return False

        return self._search()

    def _search(self) -> bool:
        if self.all_assigned():
            return True

        decision_lit = self.choose_literal_dlis()
        if decision_lit is None:
            return True

        self.decisions += 1
        parent_level = self.current_level

        for branch_lit in (decision_lit, -decision_lit):
            self.current_level += 1
            self.trail_limits.append(len(self.trail))

            ok = self.assign_literal(branch_lit, self.current_level, None)
            if ok:
                conflict = self.propagate()
                if conflict is None:
                    if self._search():
                        return True
                else:
                    jump_level = self.compute_backjump_level(conflict)
                    if jump_level < parent_level:
                        jump_level = parent_level
                    self.backjumps += 1
                    self.backtrack_to_level(jump_level)
                    if self.current_level < parent_level + 1:
                        continue

            if self.current_level > parent_level:
                self.backtrack_to_level(parent_level)

        return False

    def final_assignment(self) -> List[int]:
        out = [0] * (self.n + 1)
        for var in range(1, self.n + 1):
            out[var] = 0 if self.assignment[var] == -1 else self.assignment[var]
        return out


def format_sat_output(assignment: List[int]) -> str:
    return "RESULT:SAT\nASSIGNMENT:" + " ".join(
        f"{i}={assignment[i]}" for i in range(1, len(assignment))
    )


def format_unsat_output() -> str:
    return "RESULT:UNSAT"


def main() -> int:
    if len(sys.argv) != 2:
        print("Usage: python3 SAT1.py benchmark.cnf", file=sys.stderr)
        return 1

    try:
        formula = parse_dimacs_cnf(sys.argv[1])
        solver = SATSolver(formula)
        sat = solver.solve()
        if sat:
            print(format_sat_output(solver.final_assignment()))
        else:
            print(format_unsat_output())
        return 0
    except Exception as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
