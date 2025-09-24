# Assignment: SAT Solving and Graph 3-Coloring in Haskell

This project focuses on implementing a small SAT solver in Haskell, inspired by classical algorithms such as *DPLL* (Davis–Putnam–Logemann–Loveland) and *CDCL* (Conflict-Driven Clause Learning).  

The solver is later applied to the **graph 3-coloring problem**, another NP-complete problem.


## Stage 1: Basic SAT Solver

This stage covers:

- Representing Boolean formulas in *Conjunctive Normal Form* using Haskell data structures:
  - Variable: positive integer (e.g., x1 → 1)
  - Literal: non-zero integer with sign indicating polarity (x1 → 1, ¬x1 → -1)
  - Clause: set of literals (e.g., {1, -2, 3})
  - Formula: set of clauses (e.g., {{1, -2, 3}, {-4, 5}})
  - Interpretation: set of assumed true literals (e.g., {1, -2})

- Implementing basic operations for these representations.

- Create a naive satisfiability checker by enumerating all possible interpretations.

-  Working with sets (Data.Set) instead of lists, to enforce uniqueness and order irrelevance.

Main goal is getting a better grasp on higher-order functions, list comprehensions, and lazy evaluation.


## Stage 2: Smarter SAT Solver

This stage covers:

- Working with a new representation:
  - Associative maps (Data.Map) are used to track both the original and reduced form of clauses.

- Observing the formula after each new assumption, instead of generating full interpretations.

- Applying elimination rules:
  - If a clause contains the assumed literal → remove the clause.
  - If a clause contains the negation of the literal → remove the negated literal.

- Detecting:
  - Unit clauses → must be satisfied immediately.
  - Pure literals → can be safely assumed without conflicts.

Main goals are working with associative arrays and their functional operations (Map.map, Map.filterWithKey, etc.), while also strengthening skills reagrding user-defined data types and pattern matching.


## Stage 3: Full Solver with Clause Learning

This stage covers:

- Backtracking when a conflict (empty clause) appears.

- Non-chronological backtracking by learning new clauses that prevent repeating the same conflicts.

- Resolution of clauses to identify conflicting assumptions.

- Application of the SAT solver to graph 3-coloring:
  - Each node has exactly one of three colors (Red, Green, Blue).
  - Adjacent nodes must have different colors.
  - Constraints are encoded in CNF, solved by the SAT solver, and then decoded back into a coloring.

The key components here are clause learning and resolution, polymorphism and type classes and SAT-based reduction of graph coloring.


## Project Structure

- Formula.hs → Stage 1 (basic CNF operations and naive solver)

- ExtendedFormula.hs → Stage 2 (map-based representation, unit clauses, pure literals)

- Solver.hs → Stage 3 (conflict analysis, clause learning, graph 3-coloring)
