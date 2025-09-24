module ExtendedFormula where

import Formula

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Arrow ((&&&), second)
import Data.List (intercalate)

{-
The extended representation of formulas is necessary because we will
start to eliminate literals from formulas, but the solving algorithms
require both the current form of the clauses and the original form.

Therefore, instead of a simple set of clauses, as in phase 1, we use an
associative table (Map), in which the keys are the current clauses, subject
to the elimination process, and the values ​​are the original clauses. Each
current clause corresponds to the original clause from which it was obtained
by elimination.

In the following, we will call the formulas in phase 1 (Formula) simple
formulas, in contrast to the extended formulas defined here
(ExtendedFormula).
-}
type ExtendedFormula = Map Clause Clause

{-
An action performed on a formula can be:

* Unit literal clause: removing the only literal from a unit clause.
  "clause" represents the original clause from which the unit clause was
  obtained.
  For example, if the unit clause {1} was obtained from the original
  clause {1, 2} by a previous action, the current action to remove unit
  clause {1} is Unit 1 {1, 2}, and not Unit 1 {1}, as the information would
  have become redundant!
* Pure literal: removing a pure literal.
* Decide literal: removing a random literal.
* NOP: no effect operation.
-}
data Action
    = Unit   { getLiteral :: Literal, getClause :: Clause }
    | Pure   { getLiteral :: Literal }
    | Decide { getLiteral :: Literal }
    | NOP
    deriving (Show, Eq)

{-
History of actions performed, starting with the most recent action
(anti-chronological sense).

Each action appears paired with the formula it produced. We use a
stacked list, not a set, since the temporal order is
relevant. The first pair corresponds to the most recent action.
-}
type History = [(Action, ExtendedFormula)]

{-
Determines the extended representation of a simple formula. Initially, before
any deletion, their keys and values ​​coincide.

>>> extendFormula $ toFormula [[1], [-2, 3]]
fromList [(fromList [-2,3],fromList [-2,3]),(fromList [1],fromList [1])]
-}
extendFormula :: Formula -> ExtendedFormula
extendFormula = Map.fromSet id

{-
The counterpart of toFormula from phase 1.

>>> toExtendedFormula [[1], [-2, 3]]
fromList [(fromList [-2,3],fromList [-2,3]),(fromList [1],fromList [1])]
-}
toExtendedFormula :: [[Literal]] -> ExtendedFormula
toExtendedFormula = extendFormula . toFormula

{-
Determines the simple formula of an extended formula. Of interest is
the current version of the extended formula, captured by keys, which reflects
the actions performed, not the original version, captured by values.

>>> baseFormula $ toExtendedFormula [[1], [-2, 3]]
fromList [fromList [-2,3],fromList [1]]
-}
baseFormula :: ExtendedFormula -> Formula
baseFormula = Map.keysSet

{-
Allows a more readable view of an action history, by applying
the HV data constructor to the history. Formulas produced
by actions, captured by the map keys, are highlighted.

>>> HV [(NOP, toExtendedFormula [[1], [-2, 3]]), (NOP, toExtendedFormula [[4]])]
NOP => [[-2,3],[1]]
NOP => [[4]]
-}
newtype HistoryVisualizer = HV History
instance Show HistoryVisualizer where
    show (HV history) =
        intercalate "\n" $
        map (\(action, formula) ->
            show action ++ " => " ++
            show (toLiteralLists (baseFormula formula)))
        history

{-
Implement the promote function, which promotes a function that operates on a
simple formula, to a function that operates on an extended formula. The function
helps us to reuse certain functions defined on simple formulas, without
needing to redefine them from scratch for extended formulas.

CONSTRAINTS:

* Use the point-free style.

Examples:

>>> promote formulaLiterals $ toExtendedFormula [[1, 2], [-2]]
fromList [-2,1,2]
-}
promote :: (Formula -> a) -> ExtendedFormula -> a
promote = (. baseFormula)

{-
Implement the function eliminate, which removes a literal assumed to be
true from an extended formula. At key level, this means that:

* All clauses containing the literal disappear.
* All occurrences of the literal's complement in the remaining clauses disappear.

CONSTRAINTS:

* Avoid explicit recursion by leveraging array functions and the functions
  defined above.
* Use point-free style in the formula parameter; you can still explicitly
  specify the literal parameter.

Examples:

>>> eliminate 1 $ toExtendedFormula [[1, 2], [-1, 3]]
fromList [(fromList [3],fromList [-1,3])]

Above, the clause {1, 2} disappears, and from the clause {-1, 3} the literal -1
disappears.

>>> eliminate (-1) $ toExtendedFormula [[1, 2], [-1, 3]]
fromList [(fromList [2],fromList [1,2])]

Above, the clause {-1, 3} disappears, and from the clause {1, 2} the literal 1
disappears.
-}
eliminate :: Literal -> ExtendedFormula -> ExtendedFormula
eliminate literal = Map.mapKeys (\k -> Set.delete (complement literal) k)
                    . Map.filterWithKey (\k _ -> (Set.notMember literal k))

{-
Implement the function firstPureLiteral, which determines the first
pure literal in an extended formula, if it exists. The first literal
means the smallest, from the perspective of ordered sets.

Consider whether your implementation only performs calculations up to
the determination of the first pure literal or determines them all
unnecessarily.

CONSTRAINTS:

* Avoid explicit recursion, leveraging set functions and the functions
  defined above.
* Use the isPureLiteral function from phase 1.
* Use the promote function above.

Hint: Set functions visit elements in natural order.

Examples:

>>> firstPureLiteral $ toExtendedFormula [[1], [-1]]
Nothing

>>> firstPureLiteral $ toExtendedFormula [[1, 2, 3], [2, -3]]
Just 1

Above, 1 and 2 are pure literals, but the first (smallest) is 1.

>>> firstPureLiteral $ toExtendedFormula [[1, -2, -3], [-1, -2, -3]]
Just (-3)

Above, -3 and -2 are pure literals, but the first (smallest) is -3.
-}
firstPureLiteral :: ExtendedFormula -> Maybe Literal
firstPureLiteral formula =
  let pureLiterals = Set.filter (\x -> isPureLiteral x (baseFormula formula)) (promote formulaLiterals formula)
  in case null pureLiterals of
    True -> Nothing
    False -> Just (Set.elemAt 0 pureLiterals)

{-
Implement the firstUnitClause function, which determines the first
unitary clause of an extended formula, if it exists. The first clause
means the smallest, from the perspective of ordered sets. More precisely,
if so, the function returns a pair with the unique literal of the
unitary clause, and the original clause from which the unitary clause
was obtained. The unitary clause is the key, and the original clause is
the value.

Consider whether your implementation performs calculations only up to
the determination of the first unitary clause, or does it not necessarily
determine all of them.

CONSTRAINTS:

* Avoid explicit recursion by leveraging array functions and the functions
  defined above.
* Use point-free style.
* Use the isUnitClause function from phase 1.

Hints:

* Array functions visit entries in the natural order of keys.
* Map.foldrWithKey function.

Examples:

>>> firstUnitClause $ toExtendedFormula [[1, 2], [1, 3]]
Nothing

>>> firstUnitClause $ toExtendedFormula [[1], [-1, 2]]
Just (1,fromList [1])

>>> firstUnitClause $ eliminate 1 $ toExtendedFormula [[1], [-1, 2]]
Just (2,fromList [-1,2])

Above, after removing 1, we get the unit clause {2}, which corresponds to
the original clause {-1, 2}.
-}
firstUnitClause :: ExtendedFormula -> Maybe (Literal, Clause)
firstUnitClause = Set.lookupMin
                  . Map.foldrWithKey (\k x ks -> if (isUnitClause k) then Set.insert ((Set.elemAt 0 k), x) ks else ks) Set.empty

{-
The following three functions should all be implemented as applications
of the process function:

* decide
* processPureLiterals
* processUnitClauses.

Determine the formal parameters that process should receive in order to
have all the necessary information. Ideally, if you covertly capture in
process the common parts of the three functions above, they should
become one-liners. The process function is not scored on its own.

Hint: For managing the content of a (Maybe a), you may find the
maybe function useful.
-}
process :: (ExtendedFormula -> Maybe a)
        -> (a -> ExtendedFormula -> Action)
        -> (a -> ExtendedFormula -> ExtendedFormula)
        -> Bool -> History -> History
process finder makeAction eliminator isRepeat = go
  where
    go history = case finder (snd (head history)) of
      Nothing -> history
      Just x ->
        let formula = snd (head history)
        in case isRepeat of
          True -> go ((makeAction x formula, eliminator x formula) : history)
          False -> (makeAction x formula, eliminator x formula) : history

{-
Implement the decide function, which removes the first (smallest) literal
from an extended formula.

The function takes as a parameter an action history, which has the most
recent entry in the first position, and returns the new history, obtained
by adding a corresponding Decide action, along with the extended formula
it produces.

CONSTRAINTS:

* The entire implementation must be a partial application of the function
  process.
* Use point-free style.

Examples:

>>> HV $ decide [(NOP, toExtendedFormula [[1, -2, 3], [-3, -1, 2]])]
Decide {getLiteral = -3} => [[-2,1]]
NOP => [[-3,-1,2],[-2,1,3]]

Above, the decision is to remove the smallest literal, -3.
-}

decide :: History -> History

-- decide history = case Set.lookupMin literals of
--   Nothing -> history
--   Just deletedElem -> addition deletedElem : history
--   where
--     oldFormula = snd (head history)
--     literals = promote formulaLiterals oldFormula
--     addition lit = (Decide lit, eliminate lit oldFormula)

decide = process (Set.lookupMin . promote formulaLiterals) (\lit _ -> Decide lit) (\lit -> eliminate lit) False


{-
Implement the processPureLiterals function, which iteratively determines
and eliminates the first (smallest) pure literal from an extended formula.
Processing continues until no more pure literals are found. It is possible
for literals that were not pure to become pure after eliminating others.

The function takes as a parameter an action history, which has the most
recent entry in the first position, and returns the new history, obtained by
adding a corresponding Pure action, along with the extended formula that
produces it.

CONSTRAINTS:

* The entire implementation must be a partial application of the function
  process.
* Use point-free style.
* Use the function firstPureLiteral.

Examples:

>>> HV $ processPureLiterals [(NOP, toExtendedFormula [[1, 2], [2, 3], [-3, 4], [-4, 3]])]
Pure {getLiteral = 2} => [[-4,3],[-3,4]]
Pure {getLiteral = 1} => [[-4,3],[-3,4],[2,3]]
NOP => [[-4,3],[-3,4],[1,2],[2,3]]

Above, the first pure literal is 1, and is removed. Then, the first pure
literal becomes 2, and is also removed.

>>> HV $ processPureLiterals [(NOP, toExtendedFormula [[1, 2], [1]])]
Pure {getLiteral = 1} => []
NOP => [[1],[1,2]]

Above, the first pure literal, 1, is removed, which also leads to the
implied disappearance of pure literal 2. Therefore, (Pure 2) is no longer
added to the history.

>>> HV $ processPureLiterals [(NOP, toExtendedFormula [[1, 2], [-2, 3], [-3, -2]])]
Pure {getLiteral = -2} => []
Pure {getLiteral = 1} => [[-3,-2],[-2,3]]
NOP => [[-3,-2],[-2,3],[1,2]]

Above, 1 is initially the only pure literal, and is removed. Then, -2,
which was not pure at first, becomes pure, and is eliminated. The example
demonstrates the necessity of repeated processing of the formula.
-}
processPureLiterals :: History -> History

-- processPureLiterals history = case firstPureLiteral oldFormula of
--   Nothing -> history
--   Just deletedElem -> processPureLiterals (addition deletedElem : history)
--   where
--     oldFormula = snd (head history)
--     addition lit = (Pure lit, eliminate lit oldFormula)

processPureLiterals = process firstPureLiteral (\lit _ -> Pure lit) (\lit -> eliminate lit) True


{-
Implement the processUnitClauses function, which, repeatedly, determines
and eliminates the first (smallest) unitary clause in an extended
formula. Processing continues until no more unitary clauses are found.
It is possible for clauses that were not originally unitary to become
unitary after removing some literals.

The function takes as a parameter a history of actions, which has the
most recent entry in the first position, and returns the new history,
obtained by adding a corresponding Unit action, along with the expanded
formula it produces.

CONSTRAINTS:

* The entire implementation must be a partial application of the process
  function.
* Use the point-free style.
* Use the firstUnitClause function.

Examples:

>>> HV $ processUnitClauses [(NOP, toExtendedFormula [[1, 2], [1, 3], [2], [3]])]
Unit {getLiteral = 3, getClause = fromList [3]} => []
Unit {getLiteral = 2, getClause = fromList [2]} => [[1,3],[3]]
NOP => [[1,2],[1,3],[2],[3]]

Above, the first unit clause is {2}, and it is removed. Then, the first
unit clause becomes {3}, also removed.

>>> HV $ processUnitClauses [(NOP, toExtendedFormula [[1], [-2, -1]])]
Unit {getLiteral = -2, getClause = fromList [-2,-1]} => []
Unit {getLiteral = 1, getClause = fromList [1]} => [[-2]]
NOP => [[-2,-1],[1]]

Above, {1} is initially the only unitary clause, and is removed. Then,
clause {-2, -1}, which was initially not unitary, becomes unitary
after removing literal 1 from the formula, and is removed. Once again,
notice that in the Unit action, the original clause {-2, -1} from which
the unitary clause {-2} was obtained is stored, not the unitary clause
itself. The example demonstrates the necessity of repeated processing
of the formula.
-}
processUnitClauses :: History -> History

-- processUnitClauses history = case firstUnitClause oldFormula of
--   Nothing -> history
--   Just pair -> processUnitClauses (addition pair : history)
--   where
--     oldFormula = snd (head history)
--     addition pair = (uncurry Unit pair, eliminate (fst pair) oldFormula)

processUnitClauses = process firstUnitClause (\(lit, clause) _ -> Unit lit clause) (\(lit, _) -> eliminate lit) True


{-
Sample formula
-}
formulaExample :: Formula
formulaExample = toFormula [[-4, -2, 3], [-3, 1, 2], [-1, 4]]

{-
Example history for the formula above.

>>> HV historyExample
Pure {getLiteral = -3} => []
Unit {getLiteral = -1, getClause = fromList [-1,4]} => [[-3,2]]
Decide {getLiteral = -4} => [[-3,1,2],[-1]]
NOP => [[-4,-2,3],[-3,1,2],[-1,4]]

Initially, there are no unitary clauses, nor pure literals; therefore,
the first action must be a decision. It is observed that, following
the three actions, the empty formula is obtained, which is satisfiable,
just like the original formula. It was sufficient to assume the literals
-4, -3 and -1 to be true.
-}
historyExample :: History
historyExample =
    processPureLiterals $
    processUnitClauses $
    decide [(NOP, extendFormula formulaExample)]

{-
Implement the backtrackToUnitClause function, which goes back in
history to the farthest point in the past where the clause received
as a parameter is unitary. In other words, if we traverse the list
chronologically, from the temporal origin (last entry) to the present
(first entry), the point of interest is the first encountered with the
above property. In addition, in the new history obtained, the function
adds the new clause as if it were present in the formula from the
beginning. The effect of the actions kept in the history must be
reproduced on the new clause.

CONSTRAINTS:

* Avoid explicit recursion, leveraging list functions and the functions
  defined above.
* Use point-free style in the history parameter; you can still explicitly
  specify the clause parameter.

Examples:

>>> HV $ backtrackToUnitClause (toClause [4, 5]) historyExample
Decide {getLiteral = -4} => [[-3,1,2],[-1],[5]]
NOP => [[-4,-2,3],[-3,1,2],[-1,4],[4,5]]

Above, we return to the action (Decide (-4)), undoing the effect of
the more recent actions (Pure (-3)) and (Unit (-1) {-1, 4}). This is
the first action in the chronological sense that makes the clause {4, 5}
become unitary. It would have remained unitary after the more recent
actions (Unit (-1) { -1, 4}) and (Pure (-3)), but we want to go back as
far into the past as possible. Additionally, the versions of clause {4, 5}
are added to the versions of the original formula.
-}
backtrackToUnitClause :: Clause -> History -> History
backtrackToUnitClause clause = snd . foldr combine (clause, [])
  where
    combine (action, formula) acc@(clause', history) = case action of
        NOP -> buildNewAcc clause'
        _
            | isUnitClause clause' -> acc
            | otherwise -> buildNewAcc $
                           Set.delete (complement (getLiteral action)) clause'
      where
        buildNewAcc cls =
            (cls, (action, Map.insert cls clause formula) : history)
