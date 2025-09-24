module Formula where

import Data.Set (Set)
import qualified Data.Set as Set

import Debug.Trace

{-
A Boolean variable is represented by a positive integer: 1, 2, etc.

type introduces a type synonym, similar to typedef in C.
-}
type Variable = Int

{-
A Boolean literal represents a variable or its negation.

It is represented by a nonzero integer: 1, 2, -1, -2, etc. The polarity of the
literal is captured by the sign of the integer; for example, the literal 1
designates the variable 1, and the literal -1, its negation. The integer 0 is
excluded because it would prevent the polarities from being distinguished.
-}
type Literal = Int

{-
A clause is a disjunction of literals.

It is represented as an ordered set of literals. This representation naturally
captures the uniqueness and order irrelevance of literals in the clause,
and allows for efficient searching.
-}
type Clause = Set Literal

{-
A CNF formula is a conjunction of clauses.

It is represented as an ordered set of clauses.
-}
type Formula = Set Clause

{-
An interpretation is a set of literals assumed to be true.

For example, the interpretation {1, -2} assumes that literals 1 and -2
are true, that is, variable 1 is true, and variable 2 is false.
-}
type Interpretation = Set Literal

{-
Constructs a clause from a list of literals.
-}
toClause :: [Literal] -> Clause
toClause = Set.fromList

{-
Constructs a formula from a list of lists of literals.
-}
toFormula :: [[Literal]] -> Formula
toFormula = Set.fromList . map toClause

{-
Transform a formula into a list of lists of literals, for readability.
-}
toLiteralLists :: Formula -> [[Literal]]
toLiteralLists = map Set.toList . Set.toList

{-
Implement the literalVariable function, which determines the variable
referenced by a literal.

CONSTRAINTS:

* Use point-free style.

Examples:

>>> literalVariable 1
1

>>> literalVariable (-1)
1

Note the placement of (-1) in parentheses. Their absence, as in
literalVariable -1, would have caused 1 to be subtracted from literalVariable,
a meaningless operation.
-}
literalVariable :: Literal -> Variable
literalVariable = abs

{-
Implement the isPositive function, which checks whether the polarity
of a literal is positive.

CONSTRAINTS:

* Use point-free style.

Examples:

>>> isPositive 1
True

>>> isPositive (-1)
False
-}
isPositive :: Literal -> Bool
isPositive = (> 0)

{-
Implement the isNegative function, which checks whether the polarity
of a literal is negative.

CONSTRAINTS:

* Use point-free style.

Examples:

>>> isNegative 1
False

>>> isNegative (-1)
True
-}
isNegative :: Literal -> Bool
isNegative = (< 0)

{-
Implement the complement function, which determines the complementary literal.

CONSTRAINTS:

* Use the point-free style.

Examples:

>>> complement 1
-1

>>> complement (-1)
1
-}
complement :: Literal -> Literal
complement = (0 -)

{-
Implement the formulaLiterals function, which determines the set of all
literals in a formula.

CONSTRAINTS:

* Avoid explicit recursion by leveraging set functions
  and the functions defined above.
* Use the point-free style.

Examples:

>>> formulaLiterals $ toFormula [[1, -2, 3], [-1, 2, 3]]
fromList [-2,-1,1,2,3]

Notice how the literals are implicitly ordered in the set.
-}
formulaLiterals :: Formula -> Set Literal
formulaLiterals = Set.foldl (\acc x -> Set.union x acc) Set.empty

{-
Implement the clauseVariables function, which determines the set of all
variables in a clause.

CONSTRAINTS:

* Avoid explicit recursion by leveraging set functions
  and the functions defined above.
* Use the point-free style.

Examples:

>>> clauseVariables $ toClause [1, -2, -1]
fromList [1,2]
-}
clauseVariables :: Clause -> Set Variable
clauseVariables = Set.map literalVariable

{-
Implement the formulaVariables function, which determines the set of all
variables in a formula.

CONSTRAINTS:

* Avoid explicit recursion, by leveraging set functions
  and the functions defined above.
* Use point-free style.

Examples:

>>> formulaVariables $ toFormula [[1, -2], [-1, 2, 3]]
fromList [1,2,3]
-}
formulaVariables :: Formula -> Set Variable
formulaVariables = Set.map literalVariable . formulaLiterals

{-
Implement the isPureLiteral function, which checks whether a literal is pure
in a formula, in the sense of the absence of its complement in that formula.

CONSTRAINTS:

* Avoid explicit recursion, leveraging set functions
  and the functions defined above.
* Use point-free style in the formula parameter; you can still make
  the literal parameter explicit.

Examples:

>>> isPureLiteral 1 $ toFormula [[1, -2, 3], [-1, 2, 3]]
False

>>> isPureLiteral 2 $ toFormula [[1, -2], [-1, 2, 3]]
False

>>> isPureLiteral 3 $ toFormula [[1, -2, 3], [-1, 2, 3]]
True

>>> isPureLiteral 3 $ toFormula [[1, -2], [-1, 2, 3]]
True
-}
isPureLiteral :: Literal -> Formula -> Bool
isPureLiteral literal = not . Set.member (complement literal) . formulaLiterals

{-
Implement the isUnitClause function, which checks whether a clause is unitary,
i.e., contains a single literal.

CONSTRAINTS:

* Use point-free style.

Examples:

>>> isUnitClause $ toClause [1]
True

>>> isUnitClause $ toClause [1, 2]
False
-}
isUnitClause :: Clause -> Bool
isUnitClause = (== 1) . Set.size

{-
Implement the isValidClause function, which checks whether a clause is
always true, in the sense that it contains both a literal and its
complement.

CONSTRAINTS:

* Avoid explicit recursion, by leveraging set functions
  and the functions defined above.
* Use sections, i.e. infixed partial applications, of the form (x `f`) or
  (`f` y).

Hint: the any function.

Examples:

>>> isValidClause $ toClause []
False

>>> isValidClause $ toClause [-1, 1, 2]
True

>>> isValidClause $ toClause [1, 2]
False
-}
isValidClause :: Clause -> Bool
isValidClause clause = any (\x -> (complement x) `elem` clause) clause

{-
Implement the isValidFormula function, which checks whether a formula is
always true, in the sense that all of its clauses are always true.

CONSTRAINTS:

* Avoid explicit recursion, leveraging set functions
  and the functions defined above.
* Use point-free style.

Hint: the all function.

Examples:

>>> isValidFormula $ toFormula []
True

>>> isValidFormula $ toFormula [[1, -1, 2], [-2, 2, 3]]
True

>>> isValidFormula $ toFormula [[1, -1, 2], [-2, 3]]
False
-}
isValidFormula :: Formula -> Bool
isValidFormula = all (isValidClause)

{-
*** TODO ***

Implement the satisfiesFormula function, which checks whether an interpretation
satisfies a formula, in the sense that, assuming the literals in the
interpretation are true, the formula is true.

CONSTRAINTS:

* Avoid explicit recursion by leveraging set functions
  and the functions defined above.
* Use point-free style in the formula parameter; you can still explicitly
  specify the interpretation parameter.

Examples:

>>> satisfiesFormula (Set.fromList [1, -2]) $ toFormula [[1, 2]]
True

>>> satisfiesFormula (Set.fromList [1, -2]) $ toFormula [[1, 2], [2]]
False

>>> satisfiesFormula (Set.fromList [1, -2]) $ toFormula [[1, 2], [-2]]
True
-}
satisfiesFormula :: Interpretation -> Formula -> Bool
satisfiesFormula interpretation = all (not . Set.disjoint interpretation)

{-
Implement the interpretations function, which generates a list of all
interpretations for a set of variables.

CONSTRAINTS:

* Avoid explicit recursion, leveraging set functions
  and the functions defined above.
* Use point-free style.
* Use list comprehensions.

Examples:

>>> interpretations $ Set.empty
[fromList []]

>>> interpretations $ Set.fromList [1]
[fromList [1],fromList [-1]]

>>> interpretations $ Set.fromList [1, 2]
[fromList [1,2],fromList [-2,1],fromList [-1,2],fromList [-2,-1]]
-}

insertFunction :: [Set Literal] -> Variable -> [Set Literal]
insertFunction acc var =
  [Set.insert var currentCombinations | currentCombinations <- acc]
  ++
  [Set.insert (complement var) currentCombinations | currentCombinations <- acc]

interpretations :: Set Variable -> [Interpretation]
interpretations = Set.foldl insertFunction [Set.empty]

{-
Implement the isSatisfiable function, which checks whether a formula is
satisfiable, i.e. true in at least one interpretation.

CONSTRAINTS:

* Avoid explicit recursion, by leveraging set functions
  and the functions defined above.

Examples:

>>> isSatisfiable $ toFormula [[1, 2], [-2]]
True

>>> isSatisfiable $ toFormula [[1], [-1]]
False

>>> isSatisfiable $ toFormula []
True

>>> isSatisfiable $ toFormula [[]]
False

QUESTIONS:

1. How does lazy evaluation contribute to efficient interpretation exploration?

2. What would have happened if interpretations returned a set of
   interpretations instead of a list? Use the Debug.Trace module, already
   imported, to view the interpretations generated in the two situations.

   To simulate the return of a set from interpretations, it is sufficient to
   apply Set.fromList to the list returned by the current implementation in the
   body of isSatisfiable.

ANSWERS:

1. Since lazy evaluation is used, once an interpretation is found that
   satisfies all the requirements of the formula, no new possible interpretations
   are explored. This represents a contribution in terms of time,
   the solution time being reduced compared to the case where all the
   possibilities would have been generated and then each one tested.

2. If Set.fromList was used on the list, then it would have been necessary to
   explore all the possibilities to put them into a set, which
   would have meant a worse temporal performance than if the list is
   returned directly.
-}

isSatisfiable :: Formula -> Bool
isSatisfiable formula =
  let allVariables = formulaVariables formula
      allInterpretations = interpretations allVariables
  in any (\interp -> satisfiesFormula interp formula) allInterpretations
