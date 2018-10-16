module Heap exposing (Heap, deleteMin, empty, findMin, insert, isEmpty)

{-| A min-heap representation, used for Depth First Searching in the anytime algorithm.
May be extended to be used in other methods in the future.
-}

import Array exposing (Array)



--- Type and Indexers


{-| Internal representation is an Array, which we operate on and sort.
-}
type Heap a
    = Heap (Array a)


{-| Identify the index of the left child of the current node in the array.
-}
leftIdx i =
    2 * i + 1


{-| Identify the index of the right child of the current node in the array.
-}
rightIdx i =
    2 * i + 2


{-| Identify the index of the parent of the current node in the array.
-}
parentIdx i =
    (i - 1) // 2



--- Exposed functions


{-| An empty Heap constructor. Equivalent to an empty array constructor under the hood.
-}
empty : Heap comparable
empty =
    Heap Array.empty


{-| Check if the Heap is empty or not.
-}
isEmpty : Heap comparable -> Bool
isEmpty (Heap array) =
    Array.isEmpty array


{-| Get the minimum value in the heap. Since this is a min-heap, we can happily
grab the first value in the array.
-}
findMin : Heap comparable -> Maybe comparable
findMin (Heap array) =
    Array.get 0 array


{-| Add a value to the heap. We initially append it to the end of the array.
If it's meant to live at that position then the insertion is O(1).
if however, it needs to move to some other position due to its size, it
will bubble up higher in the array until such time as it reaches equilibrium.
Worst case therefore, this operation is O(log N).
-}
insert : comparable -> Heap comparable -> Heap comparable
insert x (Heap array) =
    array
        |> addToEnd x
        |> bubbleUp (Array.length array)
        |> Heap


{-| Removes the smallest value from the heap. This pops element 0 (i.e. the smallest value),
moves the lastElement (the largest value) to the root, then bubbles down to reorder the heap.
-}
deleteMin : Heap comparable -> Maybe ( comparable, Heap comparable )
deleteMin (Heap array) =
    case removeFromEnd array of
        Nothing ->
            Nothing

        Just ( lastElement, choppedArray ) ->
            let
                minElement =
                    unsafeGet 0 array

                newArray =
                    choppedArray
                        |> Array.set 0 lastElement
                        |> bubbleDown 0
            in
            Just ( minElement, Heap newArray )



--- Helper functions


{-| Append a value to the end of the array.
-}
addToEnd : a -> Array a -> Array a
addToEnd =
    Array.push


{-| Separate the value at the end from the array.
-}
removeFromEnd : Array a -> Maybe ( a, Array a )
removeFromEnd array =
    let
        n =
            Array.length array
    in
    case Array.get (n - 1) array of
        Nothing ->
            Nothing

        Just last ->
            Just ( last, Array.slice 0 -1 array )


{-| An unsafe method to get values from the array.
-}
unsafeGet : Int -> Array a -> a
unsafeGet i array =
    case Array.get i array of
        Just x ->
            x

        Nothing ->
            Debug.todo "handle this"


{-| Swap data between two locations in the array.
-}
swap : Int -> Int -> Array a -> Array a
swap idx1 idx2 array =
    let
        data1 =
            unsafeGet idx1 array

        data2 =
            unsafeGet idx2 array
    in
    array |> Array.set idx1 data2 |> Array.set idx2 data1


{-| Move value at a certain index up the array in relation to the heap's sorting requirements.
-}
bubbleUp : Int -> Array comparable -> Array comparable
bubbleUp idx array =
    let
        child =
            unsafeGet idx array

        parent =
            unsafeGet (parentIdx idx) array
    in
    if parent <= child then
        array

    else
        array |> swap idx (parentIdx idx) |> bubbleUp (parentIdx idx)


{-| Move value at a certain index down the array in relation to the heap's sorting requirements.
-}
bubbleDown : Int -> Array comparable -> Array comparable
bubbleDown idx array =
    let
        n =
            Array.length array

        smaller tidx acc =
            if tidx < n && unsafeGet tidx array < unsafeGet acc array then
                tidx

            else
                acc

        smallest =
            idx |> smaller (leftIdx idx) |> smaller (rightIdx idx)
    in
    if idx == smallest then
        array

    else
        array |> swap idx smallest |> bubbleDown smallest
