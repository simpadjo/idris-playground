module SameElements
import Decidable.Order

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

appendSame: (h : Nat) -> (l1: List Nat) -> (l2: List Nat) -> (Same l1 l2) -> Same (h :: l1) (h :: l2)
appendSame hd t1 t2 prf = ?sdsdsdsdsdsdsds

example1 : Same [1,2] [2,1]
example1 =
          let s22 = ConsSame 2 Nil [2] (Head 2 Nil) Nils in
          let p21has1 = Tail 2 (Head 1 Nil) in
          ConsSame 1 [2] [2,1] p21has1 s22

data Sorted: (l: List Nat) -> Type where
  Empty: Sorted Nil
  Singletone: (a: Nat) -> Sorted [a]
  Prepend: (a : Nat) -> (tail : List Nat) -> (LTE a b) -> (s: Sorted (b :: tail)) -> Sorted (a :: b:: tail)

tailOfSortedIsSorted: (x : Nat) -> (xs : List Nat) -> (prf: (Sorted (x :: xs))) -> Sorted xs
tailOfSortedIsSorted h tail pr = case pr of
                                      Empty impossible
                                      (Singletone y) => Empty
                                      Prepend a tl lte prf => prf


data SortResult: (source: List Nat) -> (res : List Nat) -> Type where
  MkRes: (Same source0 res0) -> (Sorted res0)  -> SortResult source0 res0

SortResultEx : (l : List Nat) -> Type
SortResultEx l = Exists (\r => SortResult l r)

extract : (SortResultEx l) -> (List Nat)
extract (Evidence a b) = a

insertIntoNil: (h : Nat) -> (SortResultEx [h])
insertIntoNil hd = Evidence [hd] (MkRes (reflSame [hd]) (Singletone hd))

appendSmaller: (h : Nat) -> (second : Nat) -> LTE h second-> (xs: List Nat) -> (res : List Nat) -> (SortResult (second :: xs)  res) -> SortResultEx (h :: second :: xs)
appendSmaller hd x lte tail res prf = case prf of
                                         MkRes tailSame tailSorted =>
                                            let resSorted = the (Sorted (hd :: res)) (?sdf4444) in
                                            --let tailSorted1 = the (Sorted (hd :: res)) tailSorted
                                            --let sorted = the (Sorted (hd :: res)) (Prepend{b=x} hd tail lte (tailOfSortedIsSorted x tail tailSorted)) in
                                            let same = the (Same (hd :: x :: tail) (hd :: res)) (appendSame hd (x :: tail) res tailSame)  in
                                            Evidence (hd :: res) (MkRes same resSorted)

--insertLarger: (h : Nat) -> (second : Nat) -> LTE second h-> (xs: List Nat) -> (res : List Nat) -> (SortResult (second :: xs)  res) -> SortResultEx (h :: second :: xs)
--insertLarger hd x lte prf = ?sdfsdf4444

nilIsNorASortResultOfCons:  (h : Nat) -> (tail : List Nat) -> (SortResult (h :: tail) Nil) -> Void
nilIsNorASortResultOfCons = ?sppdso88

insertInto: (h : Nat) -> (tail : List Nat) -> SortResultEx tail  -> SortResultEx (h :: tail)
insertInto x xs res0 = case res0 of
                        Evidence res prf => case xs of
                          [] =>  insertIntoNil x
                          xsh :: xss =>
                              case (order{to = LTE} x xsh) of
                                  Left headIsSmaller => appendSmaller x xsh headIsSmaller xss res prf
                                  Right headIsLarger =>  let xssIsSorted = the (SortResult xss xss) ?sdfsdfsdf3 in
                                        case insertInto x xss (Evidence xss xssIsSorted) of
                                            Evidence tRes tProof =>
                                              case tRes of
                                                Nil => ?rrrImpossible
                                                rHead :: rTail => let finalRes = xsh :: rHead :: rTail in
                                                                  let fSame = the (Same (x :: xsh :: xss) finalRes ) ?iioioi in
                                                                  let fSorted = the (Sorted finalRes ) ?isdf99 in
                                                                  Evidence finalRes (MkRes fSame fSorted)





insertionSort: (l: List Nat) ->  SortResultEx l
insertionSort Nil = Evidence Nil (MkRes Nils Empty)
insertionSort (x :: xs) = insertInto x xs (insertionSort xs)
