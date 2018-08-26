module Partition exposing
    ( bruteForce
    , allPartitions, objective
    )

{-| The partition problem is a mathematically [NP-complete](https://en.wikipedia.org/wiki/NP-completeness) task
which splits a set of numbers _S_ into two subsets, where the sum of these subsets is equal.


# Methods

@docs bruteForce


# Utilities

@docs allPartitions, objective

-}

import List
import List.Extra exposing (minimumBy, scanl1)
import Tuple exposing (first, second)


{-| Directly partition your set by checking all possible permutations.
This method is best used on small sets where the solution must be accurate.

    bruteForce [ 1, 1, 1, 1, 1, 1, 6 ] == ( [ 1, 1, 1, 1, 1, 1 ], [ 6 ] )

A greedy method would distribute some ones into the second subset in the above example,
but `bruteForce` will obtain the optimal solution.

Since all possible partitons must be calculated, this is an `O(2ᴺ)` operation.

    bruteForce (List.range 0 22)

Emits a heap limit allocation failure and sets with smaller lengths take some time to compute.
So alternate methods are best once your sets get large.

-}
bruteForce : List number -> ( List number, List number )
bruteForce =
    Maybe.withDefault ( [], [] ) << minimumBy objective << allPartitions


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
Mathematically stated: `min |&sum;S₁-&sum;S₂| : S₁,S₂&sub;S`.

    objective ( [ 22, 5, 15, 3 ], [ 9, 12, 7, 11, 5, 2 ] ) == 1

    objective ( [ 7, 3, 2 ], [ 22, 5, 15, 9, 12, 11, 5 ] ) == 67

These examples are partitions from the same set. The first is a far better solution than the second.

-}
objective : ( List number, List number ) -> number
objective ( left, right ) =
    abs (List.sum left - List.sum right)
