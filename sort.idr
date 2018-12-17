module SameElements

import Data.Fin

data HasElem: (l1 : List Nat) -> (e: Nat) -> (rest: List Nat) -> Type where
  Head: (a : Nat) -> HasElem (a :: Nil) a Nil
  Tail: (h : Nat) -> (t : (HasElem l a r)) -> HasElem (h::l) a (h::r)

data Same: (l1 : List Nat) -> (l2 : List Nat) -> Type where
  Nils: Same (Nil) (Nil)
  Cons: (head1 : Nat) -> (tail1 : List Nat) -> (l2 : List Nat) -> (t : (HasElem l2 x rest2)) -> (s: Same tail1 rest2) -> Same (head1 :: tail1) l2

example1 : Same [1,2] [2,1]
example1 =
          let s22 = Cons 2 Nil [2] (Head 2) Nils in
          let p21has1 = Tail 2 (Head 1) in
          Cons 1 [2] [2,1] p21has1 s22

--data BoundedList: (b : Nat) -> (l : List Nat) -> Type where
--  Single: (a: Nat) -> BoundedList a [a]
--  AppendEq: (bounded: BoundedList b l) -> BoundedList b (b :: l)
--  AppendLess: (bounded: BoundedList b l) -> (a: Fin b) -> BoundedList a ((finToNat a) :: l)

data Sorted: (l: List Nat) -> Type where
  Empty: Sorted Nil
  Singletone: (a: Nat) -> Sorted [a]
  PrependEq: (a : Nat) -> (tail : List Nat) -> (s: Sorted (a :: tail)) -> Sorted (a :: a:: tail)
  PrependLess: (a : Fin b) -> (tail : List Nat) -> (s: Sorted (b :: tail)) -> Sorted ((finToNat a) :: b:: tail)

example2: Sorted [1,2,2,3]
example2 = PrependLess{b = 2} 1 [2,3] (PrependEq 2 [3] (PrependLess{b=3} 2 [] (Singletone 3)))

data SortResult: (source: List Nat) -> (res : List Nat) -> Type where
  MkRes: (Same source0 res0) -> (Sorted res0)  -> SortResult source0 res0

data SortResultEx : (l : List Nat) -> Type where
  MkSortResultEx : (SortResult l r) -> SortResultEx l


insertInto: (h : Nat) -> (tail : List Nat) -> (sTail : List Nat) -> (SortResult tail sTail) -> SortResultEx (h :: tail)
insertInto = ?sdfsdf

insertionSort: (l: List Nat) ->  SortResultEx l
insertionSort Nil = let res = MkRes Nils Empty in MkSortResultEx res
insertionSort (x :: xs) = let sortedTail = insertionSort xs in
                          case sortedTail of
                            MkSortResultEx aa => ?sdfsdffg
