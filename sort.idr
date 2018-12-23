module SameElements
import Decidable.Order
import Data.List

data Same: (one : List Nat) -> (other : List Nat) -> Type where
  Nils : Same [] []
  Append: (h: Nat) -> (l1 : List Nat) -> (l2 : List Nat) -> (Same l1 l2) -> Same (h :: l1) (h :: l2)
  Swap: (this:List Nat) -> (that : List Nat) ->
         (beg : List Nat) -> (x1 : Nat) -> (mid : List Nat) -> (x2 : Nat) -> (end : List Nat) ->
           (this = (beg ++ (x1 :: (mid ++ (x2 :: end))))) -> (that = (beg ++ (x2 :: (mid ++ (x1 :: end)))))  -> Same this that
  Trans: Same l1 l2 -> Same l2 l3 -> Same l1 l3

symSame: Same lst1 lst2 -> Same lst2 lst1
symSame prf = case prf of
                Nils => Nils
                Append h l1 l2 prf1  => Append h l2 l1 (symSame prf1)
                Swap this that beg x1 mid x2 end eq1 eq2 => Swap that this beg x2 mid x1 end eq2 eq1
                Trans s1 s2 => Trans (symSame s2) (symSame s1)


reflSame: (l: List Nat) -> Same l l
reflSame [] = Nils
reflSame (x :: xs) = Append x xs xs (reflSame xs)

transSame: Same lst1 lst2 -> Same lst2 lst3 -> Same lst1 lst3
transSame pr12 pr23 = ?transSame1

--tailOfSameIsSame : (h1 : Nat) -> (t1: List Nat) -> (h2 : Nat) -> (t2 : List Nat) -> Same (h1 :: t1) (h2 :: t2) -> Same t1 t2
--tailOfSameIsSame = ?sdfds0000

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

--insertIntoNil2: (h : Nat) -> (src : List Nat) -> SortResult src [] -> SortResultEx (h::src)
--insertIntoNil2 hd source (MkRes same sorted) = case same of
--                                                  Nils => Evidence [hd] (MkRes (reflSame [hd]) (Singletone hd))
--                                                  ConsSame _ _ _ _ _ impossible

--appendToConsIsNotNil : (l1 : List Nat) -> (x: Nat) -> (l2 : List Nat) -> ((l1 ++ (x :: l2)) = Nil) -> Void
--appendToConsIsNotNil [] e lst2 eq0 =
--   let pp = the (([] ++ (e :: lst2)) = []) eq0 in
--appendToConsIsNotNil (lhead :: ltail) e lst2 eq = ?sdf090

nilIsNotSameToCons: (h : Nat) -> (t : List Nat) -> (Same (h::t) Nil) -> Void
nilIsNotSameToCons = ?nilIsNotSameToCons1
--case same of
  --                                                        Nils impossible
    --                                                      Append _ _ _ _ impossible
      --                                                    Swap (hd :: tl) [] beg x1 mid x2 end eq1 eq2 =>
        --                                                    let xx = the (Nil = (beg ++ (x2 :: (mid ++ (x1 :: end))))) eq2 in ?sdfsdf2123
          --                                                Trans s1 s2 => ?sadfsda

nilIsNorASortResultOfCons:  (h : Nat) -> (tail : List Nat) -> (SortResult (h :: tail) Nil) -> Void
nilIsNorASortResultOfCons hd tl (MkRes same _) = nilIsNotSameToCons hd tl same

headDecreasesAfterSorting: (h : Nat) -> (t : List Nat) -> (newH : Nat) -> (newT : List Nat) -> (SortResult (h :: t) (newH :: newT)) -> LTE newH h
headDecreasesAfterSorting x xs nx nxs (MkRes same sorted) = case sorted of
                                                               Empty impossible
                                                               Singletone n => ?sadflkjsd
                                                               Prepend nx1 tl1 lte prf => ?sdf9888778879

appendSmaller: (next : Nat) -> (resHead : Nat) -> LTE next resHead-> (resTail: List Nat) -> SortResult (resHead :: resTail)  (resHead :: resTail) -> SortResultEx (next :: resHead :: resTail)
appendSmaller n resH lte resT prf = case prf of
                                             MkRes tailSame tailSorted =>
                                                          let resSorted = the (Sorted (n :: resH :: resT)) (Prepend{b=resH} n resT lte tailSorted)  in
                                                          let same = the (Same (n ::resH :: resT) (n :: resH :: resT)) (Append n (resH :: resT) (resH :: resT) tailSame)  in
                                                          Evidence (n :: resH :: resT) (MkRes same resSorted)

tailOfSortResIsSorted: (h: Nat) -> (tl: List Nat) -> SortResult (h::tl) (h::tl) -> SortResult tl tl
tailOfSortResIsSorted x xs (MkRes same sorted) =
                                              let tSorted = the (Sorted xs) (tailOfSortedIsSorted x xs sorted) in
                                              let tSame = reflSame xs in
                                              MkRes tSame tSorted


sortReordered : (source1 : List Nat) -> (source2 : List Nat) -> (result : List Nat) -> Same source1 source2 -> SortResult source1 result -> SortResult source2 result
sortReordered s1 s2 res same12 (MkRes same1r sorted)= let same2r = transSame (symSame same12) same1r in MkRes same2r sorted

sortIsIdempotent : (source : List Nat) -> (result : List Nat) -> SortResult source result -> SortResult result result
sortIsIdempotent src res r@(MkRes same sorted) = sortReordered src res res same r

sortReorderedEx : (source1 : List Nat) -> (source2 : List Nat) -> Same source1 source2 -> SortResultEx source1 -> SortResultEx source2
sortReorderedEx s1 s2 same (Evidence r prf) = Evidence r (sortReordered s1 s2 r same prf)

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
                                                  --let rthLTEx = the (LTE rth x) (headDecreasesAfterSorting x rTail rth rtt tProof) in
                                                  let lte2 = the (LTE rHead rth) ?sdfsdfsdf22 in--(LTEIsTransitive headIsLarger ) in
                                                  let tResIsSorted = sortIsIdempotent (x :: rTail) (rth :: rtt) tProof in
                                                  let finalRes = the (SortResultEx (rHead :: rth :: rtt) ) (appendSmaller rHead rth lte2  rtt tResIsSorted) in
                                                  let sameElements = the (Same (rHead :: rth :: rtt) (x :: rHead :: rTail)) ?sdfdsaff8888 in
                                                  sortReorderedEx  (rHead :: rth :: rtt) (x :: rHead :: rTail) sameElements finalRes

--headDecreasesAfterSorting: (h : Nat) -> (t : List Nat) -> (newH : Nat) -> (newT : List Nat) -> (SortResult (h :: t) (newH :: newT)) -> LTE h newH


insertionSort: (l: List Nat) ->  SortResultEx l
insertionSort Nil = Evidence Nil (MkRes Nils Empty)
insertionSort (x :: xs) = case insertionSort xs of
                            Evidence tailRes prf@(MkRes tSame tSorted) =>
                              let tailResIsSorted = the (SortResult tailRes tailRes) (sortIsIdempotent xs tailRes prf) in
                              let result = the (SortResultEx (x :: tailRes)) (insertInto x tailRes tailResIsSorted) in
                              let same = the (Same (x :: xs) (x :: tailRes)) (Append x xs tailRes tSame) in
                              sortReorderedEx (x :: tailRes) (x :: xs) (symSame same) result
