module Partition exposing
    ( Partition
    , bruteForce, greedy, largestDifference
    , allPartitions, objective, sumOfSets
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

@docs allPartitions, objective, sumOfSets

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


{-| Since the sums of each set need to be incuded in the greedy algorithm,
a little helper is used here to simplify the type signature.
-}
type alias GreedyHelper number =
    { s1 : number
    , s2 : number
    , partition : Partition number
    }


{-| The LDM method requires us to reduce a list, whilst keeping track of positions
(`delta(index, value)`). Then, from that reduction, a `graph` is built, traversed
and ultimately enables the construction of our balanced partition.
-}
type alias LDMSolver number =
    { graph : Graph number number, delta : List ( Int, number ) }



--- Methods


{-| Directly partition your set by checking all possible permutations.
This method is best used on small sets where the solution must be accurate.

    bruteForce [ 1, 1, 1, 1, 1, 1, 6 ] == ( [ 1, 1, 1, 1, 1, 1 ], [ 6 ] )

A [greedy](#greedy) method would distribute some ones into the second subset in the above example,
but `bruteForce` will obtain the optimal solution.

Since all possible partitons must be calculated, this is an `O(2ᴺ)` operation.

    bruteForce (List.range 0 22)

Emits a heap limit allocation failure and sets with smaller lengths take some time to compute.
So alternate methods are best once your sets get large.

-}
bruteForce : List number -> Partition number
bruteForce =
    Maybe.withDefault ( [], [] ) << minimumBy objective << allPartitions


{-| Traverse the list once i.e. `O(N)`, chosing to place the current value
into the sublist that minimises the objective at the current point in time.

The greedy method is fast and can handle large lists, but can be quite inaccurate.
Let's take a look at few examples:

    greedy [ 22, 5, 15, 3, 9, 12, 7, 11, 5, 2 ] == ( [ 11, 12, 3, 15, 5 ], [ 2, 5, 7, 9, 22 ] )

    bruteForce [ 22, 5, 15, 3, 9, 12, 7, 11, 5, 2 ] == ( [ 22, 5, 15, 3 ], [ 9, 12, 7, 11, 5, 2 ] )

Both of these partitions have [objective](#objective) values of `1`, meaning both partitions
are equivalent and equally valid.

As your lists get larger the performance of the greedy solution becomes obvious. The
[bruteForce](#bruteForce) method has issues handling lists of length `23`, whereas `greedy`
handles them near instantaneously.

    greedy (List.range 0 22) ( [ 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2 ], [ 21, 19, 17, 15, 13, 11, 9, 7, 5, 3, 1, 0 ] )

In fact, `List.range 0 500000` is really no problem.

The downfall of this method occurs when lists are weighted in such a manner that seems fine initially
(to the algorithm), but is toppled at the end of the list.

    greedy [ 1, 1, 1, 1, 1, 1, 6 ] == ( [ 1, 1, 1 ], [ 6, 1, 1, 1 ] )

-}
greedy : List number -> Partition number
greedy sequence =
    let
        result =
            greedyMap { s1 = 0, s2 = 0, partition = ( [], [] ) } sequence
    in
    result.partition


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
    bruteForce seq |> objective == 0
    largestDifference seq |> objective == 2
    greedy seq |> objective == 4

-}
largestDifference : List number -> Partition number
largestDifference sequence =
    let
        initDelta =
            List.sortWith flippedIndexedComparison <| List.indexedMap Tuple.pair sequence

        ldm =
            kkHeuristic { graph = initialiseGraph sequence, delta = initDelta }
    in
    Graph.symmetricClosure mergeEdges ldm.graph
        |> colourGraph



--- Helpers


{-| For each value in the set, the greedy algorithm checks which subset
the value should be placed in, such that the objective is minimised.
We recurse through the list and accumulate the sum of S1 and S2 as we go.
-}
greedyMap : GreedyHelper number -> List number -> GreedyHelper number
greedyMap info sequence =
    case sequence of
        [] ->
            info

        x :: xs ->
            let
                s1new =
                    info.s1 + x

                s2new =
                    info.s2 + x
            in
            if abs (s1new - info.s2) < abs (s2new - info.s1) then
                greedyMap { info | s1 = s1new, partition = ( x :: first info.partition, second info.partition ) } xs

            else
                greedyMap { info | s2 = s2new, partition = ( first info.partition, x :: second info.partition ) } xs


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
                    , graph = insertEdge (Edge idx1 idx2 difference) diff.graph
                }


{-| Select a root node and traverse the graph to identify the structure to color.
Separate the resultant set using red/black colouring.
-}
colourGraph : Graph number number -> Partition number
colourGraph graph =
    Graph.guidedDfs Graph.alongOutgoingEdges (Graph.onDiscovery (::)) (findRoot graph) [] graph
        |> Tuple.first
        |> List.map (.node >> .label)
        |> separate


{-| Check each node in the graph for exactly two edges.
Since our graph will be a spanning tree by the time this function
is called, we will identify two possible root candidates.
We take the first since it doesn't matter which direction we traverse.
-}
findRoot : Graph number number -> List Int
findRoot graph =
    Graph.nodeIds graph
        |> List.map (\node -> identifyBound node graph)
        |> List.filter ((<=) 0)
        |> List.take 1


{-| Check if the current node has two connected edges.
If so, this should be one of our 'roots' from which to traverse
the graph.

Assumes the graph is an undirected spanning tree.

-}
identifyBound : Graph.NodeId -> Graph number number -> Graph.NodeId
identifyBound node graph =
    Graph.get node graph
        |> Maybe.map
            (\ctx ->
                if IntDict.size ctx.incoming + IntDict.size ctx.outgoing == 2 then
                    ctx.node.id

                else
                    -1
            )
        |> Maybe.withDefault -1


{-| Split a list by red/black colouring
-}
separate : List number -> Partition number
separate sequence =
    case sequence of
        [] ->
            ( [], [] )

        [ one ] ->
            ( [ one ], [] )

        one :: two :: xs ->
            let
                theRest =
                    separate xs
            in
            ( one :: first theRest, two :: second theRest )


{-| Sort highest to lowest of a list zipped with indexes
-}
flippedIndexedComparison : ( a, comparable ) -> ( a, comparable ) -> Order
flippedIndexedComparison ( x, left ) ( y, right ) =
    case compare left right of
        LT ->
            GT

        EQ ->
            EQ

        GT ->
            LT


{-| Generate a graph representation of a set
-}
initialiseGraph : List number -> Graph number number
initialiseGraph sequence =
    Graph.fromNodesAndEdges (sequenceToNodes sequence) []


{-| Convert a set into a list of graph Nodes
-}
sequenceToNodes : List number -> List (Node number)
sequenceToNodes =
    List.indexedMap (\i x -> Node i x)


{-| Helper function to insert graph edges on the fly.
Currently this isn't explicitly an ability of `graph`:
[graph#19](https://github.com/elm-community/graph/issues/19)

Assumes nodes are already in the graph and will have undefined
behaviour if not.

-}
insertEdge : Edge e -> Graph n e -> Graph n e
insertEdge edge =
    Graph.update edge.from
        (\maybeCtx ->
            case maybeCtx of
                Nothing ->
                    Nothing

                Just ctx ->
                    Just { ctx | outgoing = IntDict.insert edge.to edge.label ctx.outgoing }
        )


{-| Simply take the outgoing label as our label for both edges
-}
mergeEdges : Graph.NodeId -> Graph.NodeId -> e -> e -> e
mergeEdges from to outgoingLabel incomingLabel =
    outgoingLabel



--- Utilities


{-| Generates all possible partitions of a given set of numbers.

    allPartitions [ 3, 15 ] == [ ( [ 3, 15 ], [] ), ( [ 3 ], [ 15 ] ), ( [ 15 ], [ 3 ] ), ( [], [ 3, 15 ] ) ]

Note that this function scales as `O(2ᴺ)`, where `N` is the length of your list.

-}
allPartitions : List number -> List (Partition number)
allPartitions sequence =
    case sequence of
        [] ->
            [ ( [], [] ) ]

        x :: xs ->
            let
                sub_sequence =
                    allPartitions xs
            in
            List.map (\w -> ( x :: first w, second w )) sub_sequence ++ List.map (\w -> ( first w, x :: second w )) sub_sequence


{-| The objective for our partitioning is to minimise the difference between the sum of each subset.
Mathematically stated: `min |∑S₁-∑S₂| : S₁,S₂⊂S`.

    objective ( [ 22, 5, 15, 3 ], [ 9, 12, 7, 11, 5, 2 ] ) == 1

    objective ( [ 7, 3, 2 ], [ 22, 5, 15, 9, 12, 11, 5 ] ) == 67

These examples are partitions from the same set. The first is a far better solution than the second.

-}
objective : Partition number -> number
objective ( left, right ) =
    abs (List.sum left - List.sum right)


{-| Outputs the sum of each subset to validate the quality of a partition.

    sumOfSets ( [ 22, 5, 15, 3 ], [ 9, 12, 7, 11, 5, 2 ] ) == ( 45, 46 )

-}
sumOfSets : Partition number -> ( number, number )
sumOfSets ( left, right ) =
    ( List.sum <| left, List.sum <| right )
