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
appendSame hd t1 t2 prf = ConsSame hd t1 (hd :: t2) (Head hd t2) prf

symSame: (l1 : List Nat) -> (l2 : List Nat) -> Same l1 l2 -> Same l2  l1
symSame Nil Nil prf = Nils
symSame (x::xs) Nil prf = case prf of
                             Nils impossible
                             ConsSame _ _ _ _ _ impossible
symSame  Nil (y :: ys) prf = case prf of
                              Nils impossible
                              ConsSame _ _ _ _ _ impossible
symSame (x::xs) (y ::ys) prf = case prf of
                              Nils impossible
                              ConsSame x xs (y::ys) has tProof => ?asdf333

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

--
insertIntoNil: (h : Nat) -> (SortResultEx [h])
insertIntoNil hd = Evidence [hd] (MkRes (reflSame [hd]) (Singletone hd))

insertIntoNil2: (h : Nat) -> (src : List Nat) -> SortResult src [] -> SortResultEx (h::src)
insertIntoNil2 hd source (MkRes same sorted) = case same of
                                                  Nils => Evidence [hd] (MkRes (reflSame [hd]) (Singletone hd))
                                                  ConsSame _ _ _ _ _ impossible


nilIsNorASortResultOfCons:  (h : Nat) -> (tail : List Nat) -> (SortResult (h :: tail) Nil) -> Void
nilIsNorASortResultOfCons hd tl (MkRes same _) = case same of
                                                          Nils impossible
                                                          ConsSame _ _ _ _ _ impossible

headDecreasesAfterSorting: (h : Nat) -> (t : List Nat) -> (newH : Nat) -> (newT : List Nat) -> (SortResult (h :: t) (newH :: newT)) -> LTE h newH
headDecreasesAfterSorting x xs nx nxs (MkRes same sorted) = case sorted of
                                                               Empty impossible
                                                               Singletone n => ?sadflkjsd
                                                               Prepend nx1 tl1 lte prf => ?sdf9888778879

appendSmaller: (next : Nat) -> (resHead : Nat) -> LTE next resHead-> (resTail: List Nat) -> SortResult (resHead :: resTail)  (resHead :: resTail) -> SortResultEx (next :: resHead :: resTail)
appendSmaller n resH lte resT prf = case prf of
                                             MkRes tailSame tailSorted =>
                                                          let resSorted = the (Sorted (n :: resH :: resT)) (Prepend{b=resH} n resT lte tailSorted)  in
                                                          let same = the (Same (n ::resH :: resT) (n :: resH :: resT)) (appendSame n (resH :: resT) (resH :: resT) tailSame)  in
                                                          Evidence (n :: resH :: resT) (MkRes same resSorted)

tailOfSortResIsSorted: (h: Nat) -> (tl: List Nat) -> SortResult (h::tl) (h::tl) -> SortResult tl tl
tailOfSortResIsSorted x xs (MkRes same sorted) = case sorted of
                                                     Empty impossible
                                                     Singletone _ => MkRes Nils Empty
                                                     Prepend _ _ _ srt => case same of
                                                                           Nils impossible
                                                                           ConsSame _ _ _ _ sm  => ?sdfsdfs44 --MkRes sm srt

sortIsIdempotent : (source : List Nat) -> (result : List Nat) -> SortResult source result -> SortResult result result
sortIsIdempotent src res = ?sdffsd

sortReordered : (source1 : List Nat) -> (source2 : List Nat) -> (result : List Nat) -> Same source1 source2 -> SortResult source1 result -> SortResult source2 result
sortReordered s1 s2 res same = ?sdfasdfsdf

sortReorderedEx : (source1 : List Nat) -> (source2 : List Nat) -> Same source1 source2 -> SortResultEx source1 -> SortResultEx source2
sortReorderedEx s1 s2 same = ?sdfasdfsdf

insertInto: (h : Nat) -> (lst : List Nat) -> SortResult lst lst -> SortResultEx (h :: lst)
insertInto x res prf@(MkRes _ resSorted) =
                        case res of
                          [] =>  insertIntoNil x
                          rHead :: rTail =>
                              case (order{to = LTE} x rHead) of
                                  Left headIsSmaller => appendSmaller x rHead headIsSmaller  rTail prf
                                  Right headIsLarger =>
                                    let rTailIsSorted = the (SortResult rTail rTail) (tailOfSortResIsSorted rHead rTail prf) in
                                    case insertInto x rTail rTailIsSorted of
                                      Evidence tRes tProof@(MkRes same sorted)  =>
                                              case tRes of
                                                Nil => absurd (nilIsNorASortResultOfCons x rTail tProof)
                                                rth :: rtt =>
                                                  let lte2 = the (LTE rHead rth) ?sdfppop in
                                                  let tResIsSorted = sortIsIdempotent (x :: rTail) (rth :: rtt) tProof in
                                                  let finalRes = the (SortResultEx (rHead :: rth :: rtt) ) (appendSmaller rHead rth lte2  rtt tResIsSorted) in
                                                  let sameElements = the (Same (rHead :: rth :: rtt) (x :: rHead :: rTail)) ?sdfdsaff8888 in
                                                  sortReorderedEx  (rHead :: rth :: rtt) (x :: rHead :: rTail) sameElements finalRes




insertionSort: (l: List Nat) ->  SortResultEx l
insertionSort Nil = Evidence Nil (MkRes Nils Empty)
insertionSort (x :: xs) = case insertionSort xs of
                            Evidence tailRes prf@(MkRes tSame tSorted) =>
                              let tailResIsSorted = the (SortResult tailRes tailRes) (sortIsIdempotent xs tailRes prf) in
                              let result = the (SortResultEx (x :: tailRes)) (insertInto x tailRes tailResIsSorted) in
                              let same = the (Same (x :: xs) (x :: tailRes)) (appendSame x xs tailRes tSame) in
                              sortReorderedEx (x :: tailRes) (x :: xs) (symSame (x :: xs) (x :: tailRes) same) result
