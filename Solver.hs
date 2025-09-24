module Solver where

import Formula
import ExtendedFormula

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

{-
Allows a more readable view of the result of the solve function below,
having the type (Maybe Interpretation, History).

>>> RV (Just $ Set.fromList [1, 2], historyExample)
Pure {getLiteral = -3} => []
Unit {getLiteral = -1, getClause = fromList [-1,4]} => [[-3,2]]
Decide {getLiteral = -4} => [[-3,1,2],[-1]]
NOP => [[-4,-2,3],[-3,1,2],[-1,4]]
-----
Just (fromList [1,2])
-}
newtype ResultVisualizer = RV (Maybe Interpretation, History)
instance Show ResultVisualizer where
    show (RV (mInterpretation, history)) =
        show (HV history) ++ "\n-----\n" ++ show mInterpretation

{-
Implement the resolve function, which resolves two clauses, based on
the literal received as a parameter, which is guaranteed to appear in
the first clause. The following situations are distinguished:

* If the literal's complement does not appear in the second clause,
  the function returns it unchanged.
* If the literal's complement appears in the second clause, the
  function returns the union of the two clauses, from which the literal
  and its complement are removed.

Examples:

>>> resolve 1 (toClause [1, 2]) (toClause [3])
fromList [3]

>>> resolve 1 (toClause [1, 2]) (toClause [1, 3])
fromList [1,3]

>>> resolve 1 (toClause [1, 2]) (toClause [-1, 3])
fromList [2,3]

>>> resolve (-1) (toClause [-1, 2]) (toClause [1, 3, 4])
fromList [2,3,4]
-}
resolve :: Literal -> Clause -> Clause -> Clause
resolve literal clause1 clause2 = case Set.member (complement literal) clause2 of 
  True -> Set.union (Set.delete literal clause1) (Set.delete (complement literal) clause2)
  False -> clause2

{-
Implement the learn function, which learns a new clause based on a
current clause and a list of actions in an anti-chronological sense,
corresponding to a historical one from stage 2. The following
situations are distinguished:

* Any action other than Unit is ignored.

* A Unit action requires the resolution of the original clause stored
  in the action with the current clause, based on the literal also
  stored in the action, producing a new current clause.

CONSTRAINTS:

* Avoid explicit recursion, capitalizing on list functions
  and the functions defined above.
* Use the point-free style.
* Use the resolve function.

Examples:

>>> learn (toClause [1, 2]) [Unit (-1) (toClause [-1, 3])]
fromList [2,3]

>>> learn (toClause [1, 2]) [Unit (-1) (toClause [-1, 3]), Unit (-2) (toClause [-2, 4])]
fromList [3,4]

>>> learn (toClause [1, 2]) [Pure 2, Decide 1]
fromList [1,2]
-}
isUnit :: Action -> Bool
isUnit (Unit _ _) = True
isUnit _ = False

learn :: Clause -> [Action] -> Clause
learn = foldl (\acc action -> case isUnit action of
  True -> resolve (getLiteral action) (getClause action) acc
  False -> acc)

{-
Implement the satisfy function, which takes a simple formula as a
parameter as in phase 1, and tries to satisfy it, returning a pair
with an optional interpretation, present only if the formula is
satisfiable, and the current history.

The satisfaction algorithm is as follows:

1. All unit clauses are processed (processUnitClauses function).
2. If the formula becomes empty, the original formula is satisfiable and
   the interpretation is built using the current history. STOP.
3. If the formula contains the empty clause (conflict), a new clause is
   learned (learn function).
3a. If the learned clause is empty, the formula is unsatisfiable. STOP.
3b. Otherwise, go back in history to the furthest point where the learned
    clause is unitary (backtrackToUnitClause function), and skip to step 1.
4. Process all pure literals (processPureLiterals function) and skip to
   step 1.
5. Only if there are no pure literals, assume the smallest literal
(decide function) and skip to step 1.

CONSTRAINTS:

* Use guards and pattern guards.

Examples:

>>> RV $ satisfy $ toFormula [[1, 2], [-1]]
Unit {getLiteral = 2, getClause = fromList [1,2]} => []
Unit {getLiteral = -1, getClause = fromList [-1]} => [[2]]
NOP => [[-1],[1,2]]
-----
Just (fromList [-1,2])

Above, two Unit actions satisfy the formula, and the interpretation is {-1, 2}.

>>> RV $ satisfy $ toFormula [[1, 2, 3], [2, -3], [-1]]
Pure {getLiteral = 2} => []
Unit {getLiteral = -1, getClause = fromList [-1]} => [[-3,2],[2,3]]
NOP => [[-3,2],[-1],[1,2,3]]
-----
Just (fromList [-1,2])

Above, the existence of the unitary clause {-1} first imposes the related
action, after which it is possible to eliminate the pure literal 2, which
satisfies the formula.

>>> RV $ satisfy formulaExample
Pure {getLiteral = -3} => []
Unit {getLiteral = -1, getClause = fromList [-1,4]} => [[-3,2]]
Decide {getLiteral = -4} => [[-3,1,2],[-1]]
NOP => [[-4,-2,3],[-3,1,2],[-1,4]]
-----
Just (fromList [-4,-3,-1])

Above, the example from phase 2 is resumed.

>>> RV $ satisfy $ toFormula [[-1, -2, 3], [-1, 4, -3], [-1, -4, 5], [-1, -5, -3], [1, 2, 4]]
Unit {getLiteral = 1, getClause = fromList [1,2,4]} => []
Decide {getLiteral = -2} => [[1]]
Decide {getLiteral = -3} => [[-2,-1],[1,2]]
Decide {getLiteral = -4} => [[-3,-1],[-2,-1,3],[1,2]]
Decide {getLiteral = -5} => [[-4,-1],[-3,-1,4],[-2,-1,3],[1,2,4]]
NOP => [[-5,-3,-1],[-4,-1,5],[-3,-1,4],[-2,-1,3],[1,2,4]]
-----
Just (fromList [-5,-4,-3,-2,1])

>>> RV $ satisfy $ toFormula [[1], [-1]]
Unit {getLiteral = -1, getClause = fromList [-1]} => [[]]
NOP => [[-1],[1]]
-----
Nothing

Above, the empty clause is learned, so the formula is unsatisfiable.

>>> RV $ satisfy $ toFormula [[-7, 1], [-5, 1], [-3, 4], [3, -4], [-1, 2], [1, 2], [5, 7, -2], [-6, 1, -2], [6, -1, -2]]
Unit {getLiteral = -3, getClause = fromList [-3,4]} => []
Decide {getLiteral = -4} => [[-3]]
Unit {getLiteral = 6, getClause = fromList [-2,-1,6]} => [[-4,3],[-3,4]]
Unit {getLiteral = 2, getClause = fromList [-1,2]} => [[-4,3],[-3,4],[6]]
Unit {getLiteral = 1, getClause = fromList [-5,1]} => [[-4,3],[-3,4],[-2,6],[2]]
Unit {getLiteral = 5, getClause = fromList [5,7]} => [[-6,-2,1],[-4,3],[-3,4],[-2,-1,6],[-1,2],[1],[1,2]]
Decide {getLiteral = -7} => [[-6,-2,1],[-5,1],[-4,3],[-3,4],[-2,-1,6],[-2,5],[-1,2],[1,2],[5]]
NOP => [[-7,1],[-6,-2,1],[-5,1],[-4,3],[-3,4],[-2,-1,6],[-2,5,7],[-1,2],[1,2],[5,7]]
-----
Just (fromList [-7,-4,-3,1,2,5,6])

The above example is from the statement, where the clause {5, 7} is learned.
For completeness, below is the intermediate history obtained just before
backtracking, triggered by obtaining an empty clause.

Unit {getLiteral = -1, getClause = fromList [-1,2]} => [[],[-4,3],[-3,4]]
Unit {getLiteral = -2, getClause = fromList [-2,5,7]} => [[-4,3],[-3,4],[-1],[1]]
Decide {getLiteral = -5} => [[-4,3],[-3,4],[-2],[-2,-1],[-1,2],[1,2]]
Decide {getLiteral = -6} => [[-5,1],[-4,3],[-3,4],[-2,-1],[-2,5],[-1,2],[1,2]]
Decide {getLiteral = -7} => [[-6,-2,1],[-5,1],[-4,3],[-3,4],[-2,-1,6],[-2,5],[-1,2],[1,2]]
NOP => [[-7,1],[-6,-2,1],[-5,1],[-4,3],[-3,4],[-2,-1,6],[-2,5,7],[-1,2],[1,2]]
-}
isUnitClausePresent :: ExtendedFormula -> Bool
isUnitClausePresent extendedFormula
  | firstUnitClause extendedFormula == Nothing = False
  | otherwise = True

isPureLiteralPresent :: ExtendedFormula -> Bool
isPureLiteralPresent extendedFormula
  | firstPureLiteral extendedFormula == Nothing = False
  | otherwise = True

isolateActions :: History -> [Action]
isolateActions history = foldr (\x acc -> (fst x) : acc) [] history

cycleHistory :: History -> History
cycleHistory oldHistory
  | Map.null currentFormula = unitProcessedHistory -- Check if formula is satisfied
  | Map.lookup Set.empty currentFormula /= Nothing =
    case Map.lookup Set.empty currentFormula of
      Just conflictClause -> 
        let learnedClause = learn conflictClause (isolateActions unitProcessedHistory)
        in case Set.null learnedClause of -- Check if learned clause is null 
          True -> unitProcessedHistory
          False -> cycleHistory (backtrackToUnitClause learnedClause unitProcessedHistory)
      otherwise -> unitProcessedHistory
  | isPureLiteralPresent currentFormula = cycleHistory (processPureLiterals unitProcessedHistory)
  | otherwise = cycleHistory (decide unitProcessedHistory)
  where
    unitProcessedHistory = processUnitClauses oldHistory
    currentFormula = snd (head unitProcessedHistory)

satisfy :: Formula -> (Maybe Interpretation, History)
satisfy formula
  | Map.null endResultFormula = (Just interpretation, newHistory)
  | otherwise = (Nothing, newHistory)
  where
    initialHistory = [(NOP, extendFormula formula)]
    newHistory = cycleHistory initialHistory
    endResultFormula = snd (head newHistory)
    interpretation = foldl (\acc (x, _) -> case x of
              Unit lit _ -> Set.insert lit acc
              Decide lit -> Set.insert lit acc
              Pure lit -> Set.insert lit acc
              _ -> acc) Set.empty newHistory

{-
Class whose instances represent problems reducible to SAT.

The class is parameterized with the problem variable, and contain
two functions:

* encode transforms a problem instance into a SAT instance, constructing
  the corresponding formula.
* decode transforms an interpretation into the solution of the original
  problem.

The problem variable refers to an instance of a problem, which contains
information about both the input, used by encode and decode, and about
the output, populated by decode. The presence of information about the
output within the same representation that contains information about
the input can be useful, for example, if a partial solution is required
even before encoding.
-}
class Reducible problem where
    encode :: problem -> Formula
    decode :: Interpretation -> problem -> problem

{-
Allows solving a problem by reducing to and then from SAT.
-}
reduceSolve :: Reducible problem => problem -> Maybe problem
reduceSolve problem = fmap (`decode` problem) $ fst $ satisfy $ encode problem

{-
Data types required to represent the 3-coloring problem.

* Node is the type of a node in the graph.
* Graph is the representation of an undirected graph, as sets of nodes
  and edges.
* Color denotes the three possible colors.
* ThreeColoring is the representation of an instance of the 3-coloring
  problem, where the graph field designates the input, and the coloring
  field designates the output. Although we will not use this, the coloring
  field could be partially populated from the beginning, before the reduction
  to SAT, if it is desired to impose a priori colors on certain nodes.
-}
type Node = Int

data Graph = Graph
    { nodes :: Set Node
    , edges :: Set (Node, Node)
    } deriving (Show, Eq)

data Color = Red | Green | Blue
    deriving (Show, Eq)

type Coloring = Map Node Color

data ThreeColoring = ThreeColoring
    { graph    :: Graph     -- intrarea
    , coloring :: Coloring  -- ieșirea
    } deriving (Show, Eq)

{-
Instantiate the Reducible class with type ThreeColoring, implementing
the functions encode and decode.
-}
generatePairs :: [a] -> [(a, a)]
generatePairs [] = []
generatePairs (x:xs) = [(x, y) | y <- xs] ++ (generatePairs xs)

instance Reducible ThreeColoring where
{-
>>> toLiteralLists $ encode $ ThreeColoring graph2 Map.empty
[[-23,-22],[-23,-21],[-23,-13],[-22,-21],[-22,-12],[-21,-11],[-13,-12],[-13,-11],[-12,-11],[11,12,13],[21,22,23]]

>>> toLiteralLists $ encode $ ThreeColoring graph3 Map.empty
[[-33,-32],[-33,-31],[-33,-23],[-33,-13],[-32,-31],[-32,-22],[-32,-12],[-31,-21],[-31,-11],[-23,-22],[-23,-21],[-23,-13],[-22,-21],[-22,-12],[-21,-11],[-13,-12],[-13,-11],[-12,-11],[11,12,13],[21,22,23],[31,32,33]]
-}
    encode :: ThreeColoring -> Formula
    encode problem = Set.union (Set.union atLeastOneColor atMostOneColor) neighboringEdges
      where
        graphNodes = nodes (graph problem)
        graphEdges = edges (graph problem)
        multiplyNodes x = [10 * x + 1, 10 * x + 2, 10 * x + 3]
        atLeastOneColor = Set.map (\x -> Set.fromList (multiplyNodes x)) graphNodes
        atMostOneColor = Set.fromList [Set.fromList [-a, -b] | nodes <- Set.toList graphNodes, (a, b) <- generatePairs (multiplyNodes nodes)]
        neighboringEdges = Set.fromList [Set.fromList [-n1, -n2] | (c, d) <- Set.toList graphEdges, (n1, n2) <- zip (multiplyNodes c) (multiplyNodes d)]
    
{-
>>> coloring $ decode (Set.fromList [-23,-22,-13,-11,12,21]) $ ThreeColoring graph2 Map.empty
fromList [(1,Green),(2,Red)]

>>> coloring $ decode (Set.fromList [-33,-32,-23,-21,-12,-11,13,22,31]) $ ThreeColoring graph3 Map.empty
fromList [(1,Blue),(2,Green),(3,Red)]
-}
    decode :: Interpretation -> ThreeColoring -> ThreeColoring
    decode interpretation problem = ThreeColoring (graph problem) colors
      where
        literalColor lit
          | (lit `mod` 10) == 1 = Red
          | (lit `mod` 10) == 2 = Green
          | (lit `mod` 10) == 3 = Blue
        colors = Map.fromList [(l `div` 10, literalColor l) | l <- Set.toList (Set.filter isPositive interpretation)]

{-
Examples of undirected graphs.

>>> reduceSolve $ ThreeColoring graph2 Map.empty
Just (ThreeColoring {graph = Graph {nodes = fromList [1,2], edges = fromList [(1,2)]}, coloring = fromList [(1,Green),(2,Red)]})

>>> reduceSolve $ ThreeColoring graph3 Map.empty
Just (ThreeColoring {graph = Graph {nodes = fromList [1,2,3], edges = fromList [(1,2),(1,3),(2,3)]}, coloring = fromList [(1,Blue),(2,Green),(3,Red)]})
-}
graph2 :: Graph
graph2 = Graph
    { nodes = Set.fromList [1, 2]
    , edges = Set.fromList [(1, 2)]
    }

graph3 :: Graph
graph3 = Graph
    { nodes = Set.fromList [1, 2, 3]
    , edges = Set.fromList [(1, 2), (1, 3), (2, 3)]
    }
