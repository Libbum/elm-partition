module Partition exposing
    ( bruteForce, greedy
    , allPartitions, objective, sumOfSets
    )

{-| The partition problem is a mathematically [NP-complete](https://en.wikipedia.org/wiki/NP-completeness) task
which splits a set of numbers _S_ into two subsets, where the sum of these subsets is equal.

Depending on the algorithm, order of subsets may not be preserved. If order perservation
is something you require: please file a request in the issue tracker.


# Methods

@docs bruteForce, greedy


# Utilities

@docs allPartitions, objective, sumOfSets

-}

import List
import List.Extra exposing (minimumBy, scanl1)
import Tuple exposing (first, second)


{-| Directly partition your set by checking all possible permutations.
This method is best used on small sets where the solution must be accurate.

    bruteForce [ 1, 1, 1, 1, 1, 1, 6 ] == ( [ 1, 1, 1, 1, 1, 1 ], [ 6 ] )

A <greedy> method would distribute some ones into the second subset in the above example,
but `bruteForce` will obtain the optimal solution.

Since all possible partitons must be calculated, this is an `O(2ᴺ)` operation.

    bruteForce (List.range 0 22)

Emits a heap limit allocation failure and sets with smaller lengths take some time to compute.
So alternate methods are best once your sets get large.

-}
bruteForce : List number -> ( List number, List number )
bruteForce =
    Maybe.withDefault ( [], [] ) << minimumBy objective << allPartitions


{-| Traverse the list once i.e. `O(N)`, chosing to place the current value
into the sublist that minimises the objective at the current point in time.

The greedy method is fast and can handle large lists, but can be quite inaccurate.
Let's take a look at few examples:

    greedy [ 22, 5, 15, 3, 9, 12, 7, 11, 5, 2 ] == ( [ 11, 12, 3, 15, 5 ], [ 2, 5, 7, 9, 22 ] )

    bruteForce [ 22, 5, 15, 3, 9, 12, 7, 11, 5, 2 ] == ( [ 22, 5, 15, 3 ], [ 9, 12, 7, 11, 5, 2 ] )

Both of these partitions have <objective> values of `1`, meaning both partitions
are equivalent and equally valid.

As your lists get larger the performance of the greedy solution becomes obvious. The
<bruteForce> method has issues handling lists of length `23`, whereas `greedy`
handles them near instantaneously.

    greedy (List.range 0 22) ( [ 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 2 ], [ 21, 19, 17, 15, 13, 11, 9, 7, 5, 3, 1, 0 ] )

In fact, `List.range 0 500000` is really no problem.

The downfall of this method occurs when lists are weighted in such a manner that seems fine initially
(to the algorithm), but is toppled at the end of the list.

    greedy [ 1, 1, 1, 1, 1, 1, 6 ] == ( [ 1, 1, 1 ], [ 6, 1, 1, 1 ] )

-}
greedy : List number -> ( List number, List number )
greedy sequence =
    let
        result =
            greedyMap { s1 = 0, s2 = 0, partition = ( [], [] ) } sequence
    in
    result.partition


{-| Since the sums of each set need to be incuded, a little helper
is used here to simplify the type signature.
-}
type alias GreedyHelper number =
    { s1 : number
    , s2 : number
    , partition : ( List number, List number )
    }


{-| Identifies the sum of each list. This is effectively the greedy
method's objective function.
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


{-| Generates all possible partitions of a given set of numbers.

    allPartitions [ 3, 15 ] == [ ( [ 3, 15 ], [] ), ( [ 3 ], [ 15 ] ), ( [ 15 ], [ 3 ] ), ( [], [ 3, 15 ] ) ]

Note that this function scales as `O(2ᴺ)`, where `N` is the length of your list.

-}
allPartitions : List number -> List ( List number, List number )
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
objective : ( List number, List number ) -> number
objective ( left, right ) =
    abs (List.sum left - List.sum right)


{-| Outputs the sum of each subset to validate the quality of a partition.

    sumOfSets ( [ 22, 5, 15, 3 ], [ 9, 12, 7, 11, 5, 2 ] ) == ( 45, 46 )

-}
sumOfSets : ( List number, List number ) -> ( number, number )
sumOfSets sets =
    ( List.sum <| first sets, List.sum <| second sets )
