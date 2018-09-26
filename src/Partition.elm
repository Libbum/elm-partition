module Partition exposing
    ( Partition
    , bruteForce, greedy, largestDifference
    , empty, allPartitions, objective, sumOfSets
    )

{-| The partition problem is a mathematically [NP-complete](https://en.wikipedia.org/wiki/NP-completeness) task
which splits a set of numbers _S_ into two subsets, where the sum of these subsets is equal.

Depending on the algorithm, order of subsets may not be preserved. If order perservation
is something you require: please file a request in the issue tracker.


# Types

@docs Partition


# Methods

@docs bruteForce, greedy, largestDifference


# Utilities

@docs empty, allPartitions, objective, sumOfSets

-}

import Graph exposing (Edge, Graph, Node)
import IntDict
import List
import List.Extra exposing (minimumBy, scanl1)
import Tuple exposing (first, second)



--- Type Aliases


{-| The resultant partition: two balanced subsets of the original set
-}
type alias Partition number =
    ( List number, List number )


{-| The LDM method requires us to reduce a list, whilst keeping track of positions
(`delta(index, value)`). Then, from that reduction, a graph is built with each value
in the set as nodes, connected via edges which are identified here.
-}
type alias LDMSolver number =
    { delta : List ( Int, number ), edges : List (Edge number) }



--- Methods


{-| Directly partition your set by checking all possible permutations.
This method is best used on small sets where the solution must be accurate.

    bruteForce [ 4, 5, 7, 6, 8 ]
    --> ( [ 4, 5, 6 ], [ 7, 8 ] )

This solution is a perfect partition. Since all possible partitons must be calculated,
this is an `O(2ᴺ)` operation. The [greedy](#greedy) method (for example) will partition faster,
but yields an [objective](#objective) of `4`: missing the optimal partition.

The space scaling is quite an issue for this method as well.

    bruteForce (List.range 0 22)

Emits a heap limit allocation failure and sets with smaller lengths take some time to compute.
So alternate methods are best once your sets get large.

-}
bruteForce : List number -> Partition number
bruteForce =
    Maybe.withDefault empty << minimumBy objective << allPartitions


{-| Traverse the list once i.e. `O(N)`, chosing to place the current value
into the sublist that minimises the objective at the current point in time.

The greedy method is fast and can handle large lists, but can be quite inaccurate.
Let's take a look at few examples:

    greedy [ 22, 5, 15, 3, 9, 12, 7, 11, 5, 2 ]
    --> ( [ 2, 3, 5, 9, 12, 15 ], [ 5, 7, 11, 22 ] )

    bruteForce [ 22, 5, 15, 3, 9, 12, 7, 11, 5, 2 ]
    --> ( [ 22, 5, 15, 3 ], [ 9, 12, 7, 11, 5, 2 ] )

Both of these partitions have [objective](#objective) values of `1`, meaning both partitions
are equivalent and equally valid.

As your lists get larger the performance of the greedy solution becomes obvious. The
[bruteForce](#bruteForce) method has issues handling lists of length `23`, whereas `greedy`
handles them near instantaneously.

    greedy (List.range 0 22)
    --> ( [ 0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21 ], [ 2, 3, 6, 7, 10, 11, 14, 15, 18, 19, 22 ] )

In fact, `List.range 0 500000` is really no problem.

The downfall of this method occurs when lists are weighted in such a manner that seems fine initially
(to the algorithm), but is toppled at the end of the list.

    greedy [ 4, 5, 7, 6, 8 ]
    --> ( [ 6, 7 ], [ 4, 5, 8 ] )

-}
greedy : List number -> Partition number
greedy sequence =
    List.sortWith flippedComparison sequence
        |> greedyRecurse empty


{-| The Largest Differencing Method (LDM) orders the input set and
replaces the largest two values with a difference `|x₁-x₂|`.
The resultant set is then reordered and the method is repeated until
one value is left in the list. This value is equal to the _partition difference_
of the partition.

From this differencing, a graph is generated which identifies the correct path
to follow to appropreately partition the original set.

Time complexity of this method is `O(N log N)`. List size limitations are therefore in
time moreso than space. In terms of optimality, the method sits between
[bruteForce](#bruteForce) and [greedy](#greedy):

    seq = [8,7,6,5,4]
    bruteForce seq |> objective
    --> 0
    largestDifference seq |> objective
    --> 2
    greedy seq |> objective
    --> 4

-}
largestDifference : List number -> Partition number
largestDifference sequence =
    let
        initDelta =
            List.indexedMap Tuple.pair sequence
                |> List.sortWith flippedIndexedComparison

        ldm =
            kkHeuristic
                { edges = []
                , delta = initDelta
                }
    in
    Graph.fromNodesAndEdges (sequenceToNodes sequence) ldm.edges
        |> Graph.symmetricClosure mergeEdges
        |> Graph.bfs levelSplit empty



--- Helpers


{-| Starting with an empty partition, and a list sorted higest
to lowest, identify which subset currently has the lowest sum.
Place the head of the list in that bucket and repeat.
-}
greedyRecurse : Partition number -> List number -> Partition number
greedyRecurse ( left, right ) sorted =
    case sorted of
        [] ->
            ( left, right )

        x :: xs ->
            if List.sum left < List.sum right then
                greedyRecurse ( x :: left, right ) xs

            else
                greedyRecurse ( left, x :: right ) xs


{-| The workhorse of the LDM method. Identify Delta whilst building a
graph of the optimal parth to partition.
-}
kkHeuristic : LDMSolver number -> LDMSolver number
kkHeuristic diff =
    let
        sorted =
            List.sortWith flippedIndexedComparison diff.delta
    in
    case sorted of
        [] ->
            { diff | delta = [] }

        [ x ] ->
            { diff | delta = [ x ] }

        ( idx1, one ) :: ( idx2, two ) :: theRest ->
            let
                newIdx =
                    if one > two then
                        idx1

                    else
                        idx2

                difference =
                    abs (one - two)
            in
            kkHeuristic
                { diff
                    | delta = ( newIdx, difference ) :: theRest
                    , edges = Edge idx1 idx2 difference :: diff.edges
                }


{-| A breadth-first traversal visitor which separates the tree into even and odd levels.
This is called from the `largestDifference` method once a spanning tree has been created
from the Karmarkar-Karp Heuristic. To identify the partition, the spanning tree needs to
be two-coloured, then separated. This is analagous to partitoning levels in a breadth-first
search.
-}
levelSplit : List (Graph.NodeContext n e) -> Int -> ( List n, List n ) -> ( List n, List n )
levelSplit paths distance acc =
    case paths of
        [] ->
            ( [], [] )

        ctx :: _ ->
            let
                ( left, right ) =
                    acc
            in
            if modBy 2 distance == 0 then
                ( ctx.node.label :: left, right )

            else
                ( left, ctx.node.label :: right )


{-| Sort highest to lowest
-}
flippedComparison : comparable -> comparable -> Order
flippedComparison left right =
    case compare left right of
        LT ->
            GT

        EQ ->
            EQ

        GT ->
            LT


{-| Sort highest to lowest of a list zipped with indexes
-}
flippedIndexedComparison : ( a, comparable ) -> ( a, comparable ) -> Order
flippedIndexedComparison ( x, left ) ( y, right ) =
    flippedComparison left right


{-| Convert a set into a list of graph Nodes
-}
sequenceToNodes : List number -> List (Node number)
sequenceToNodes =
    List.indexedMap (\i x -> Node i x)


{-| Simply take the outgoing label as our label for both edges
-}
mergeEdges : Graph.NodeId -> Graph.NodeId -> e -> e -> e
mergeEdges from to outgoingLabel incomingLabel =
    outgoingLabel



--- Utilities


{-| An empty partition constructor
-}
empty : Partition number
empty =
    ( [], [] )


{-| Generates all possible partitions of a given set of numbers.

    allPartitions [ 3, 15 ]
    --> [ ( [ 3, 15 ], [] ), ( [ 3 ], [ 15 ] ), ( [ 15 ], [ 3 ] ), ( [], [ 3, 15 ] ) ]

Note that this function scales as `O(2ᴺ)`, where `N` is the length of your list.

-}
allPartitions : List number -> List (Partition number)
allPartitions sequence =
    case sequence of
        [] ->
            [ empty ]

        x :: xs ->
            let
                sub_sequence =
                    allPartitions xs
            in
            List.map (\w -> ( x :: first w, second w )) sub_sequence
                ++ List.map (\w -> ( first w, x :: second w )) sub_sequence


{-| The objective for our partitioning is to minimise the difference between the sum of each subset.
Mathematically stated: `min |∑S₁-∑S₂| : S₁,S₂⊂S`.

    objective ( [ 22, 5, 15, 3 ], [ 9, 12, 7, 11, 5, 2 ] )
    --> 1

    objective ( [ 7, 3, 2 ], [ 22, 5, 15, 9, 12, 11, 5 ] )
    --> 67

These examples are partitions from the same set. The first is a far better solution than the second.

-}
objective : Partition number -> number
objective ( left, right ) =
    abs (List.sum left - List.sum right)


{-| Outputs the sum of each subset to validate the quality of a partition.

    sumOfSets ( [ 22, 5, 15, 3 ], [ 9, 12, 7, 11, 5, 2 ] )
    --> ( 45, 46 )

-}
sumOfSets : Partition number -> ( number, number )
sumOfSets ( left, right ) =
    ( List.sum <| left, List.sum <| right )
