module SameElements

import Data.Fin

data HasElem: (l1 : List Nat) -> (e: Nat) -> (rest: List Nat) -> Type where
  Head: (a : Nat) -> (t: List Nat) -> HasElem (a :: t) a t
  Tail: (h : Nat) -> (t : (HasElem l a r)) -> HasElem (h::l) a (h::r)

data Same: (l1 : List Nat) -> (l2 : List Nat) -> Type where
  Nils: Same (Nil) (Nil)
  ConsSame: (head1 : Nat) -> (tail1 : List Nat) -> (l2 : List Nat) -> (t : (HasElem l2 x rest2)) -> (s: Same tail1 rest2) -> Same (head1 :: tail1) l2

reflSame: (l: List Nat) -> Same l l
reflSame [] = Nils
reflSame (x :: xs) = let recur = the (Same xs xs) (reflSame xs) in
    ConsSame x xs (x :: xs)  (Head x xs) recur

example1 : Same [1,2] [2,1]
example1 =
          let s22 = ConsSame 2 Nil [2] (Head 2 Nil) Nils in
          let p21has1 = Tail 2 (Head 1 Nil) in
          ConsSame 1 [2] [2,1] p21has1 s22

data Sorted: (l: List Nat) -> Type where
  Empty: Sorted Nil
  Singletone: (a: Nat) -> Sorted [a]
  PrependEq: (a : Nat) -> (tail : List Nat) -> (s: Sorted (a :: tail)) -> Sorted (a :: a:: tail)
  PrependLess: (a : Fin b) -> (tail : List Nat) -> (s: Sorted (b :: tail)) -> Sorted ((finToNat a) :: b:: tail)

example2: Sorted [1,2,2,3]
example2 = PrependLess{b = 2} 1 [2,3] (PrependEq 2 [3] (PrependLess{b=3} 2 [] (Singletone 3)))

data SortResult: (source: List Nat) -> (res : List Nat) -> Type where
  MkRes: (Same source0 res0) -> (Sorted res0)  -> SortResult source0 res0

SortResultEx : (l : List Nat) -> Type
SortResultEx l = Exists (\r => SortResult l r)

extract : (SortResultEx l) -> (List Nat)
extract (Evidence a b) = a

insertIntoNil: (h : Nat) -> (SortResultEx [h])
insertIntoNil hd = Evidence [hd] (MkRes (reflSame [hd]) (Singletone hd))

insertEqual: (h : Nat) -> (xs : List Nat) -> SortResultEx (h :: xs) -> SortResultEx (h :: h :: xs)
insertEqual = ?sdsssdd

insertInto: (h : Nat) -> (tail : List Nat) -> SortResultEx tail  -> SortResultEx (h :: tail)
insertInto x xs res0 = case res0 of
                        Evidence res (MkRes tailSame tailSorted) => case xs of
                          [] =>  insertIntoNil x
                          xsh :: xss => case decEq x xsh of
                            Yes equal =>  let aux = the (SortResultEx (xsh :: xsh :: xss)) (insertEqual xsh xss res0) in
                              rewrite equal in aux
                            No notEqual => ?sd333



insertionSort: (l: List Nat) ->  SortResultEx l
insertionSort Nil = Evidence Nil (MkRes Nils Empty)
insertionSort (x :: xs) = let tailSortEx = insertionSort xs in
                          insertInto x xs tailSortEx
