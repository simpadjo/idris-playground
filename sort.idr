module SameElements
import Decidable.Order
import Data.List

data Same: (one : List Nat) -> (other : List Nat) -> Type where
  Nils : Same [] []
  Append: (h: Nat) -> (l1 : List Nat) -> (l2 : List Nat) -> (Same l1 l2) -> Same (h :: l1) (h :: l2)
  Swap: (beg : List Nat) -> (x1 : Nat) -> (mid : List Nat) -> (x2 : Nat) -> (end : List Nat)
   -> Same (beg ++ (x1 :: (mid ++ (x2 :: end)))) (beg ++ (x2 :: (mid ++ (x1 :: end))))
  Trans: Same l1 l2 -> Same l2 l3 -> Same l1 l3

lengthLemma: (l1 : List Nat) -> (l2 : List Nat) -> ((length l1) = (length l2)) -> ((length (ap ++ l1)) = (length (ap ++ l2)))
lengthLemma{ap} lst1 lst2 eq = let eq1 = the ((length (ap ++ lst1)) = ((length ap) + (length lst1))) (lengthAppend ap lst1) in
                               let eq2 = the ((length (ap ++ lst2)) = ((length ap) + (length lst2))) (lengthAppend ap lst2) in
                               let eq0 = the ( ((length ap) + (length lst1)) = ((length ap) + (length lst2))) (plusConstantLeft (length lst1) (length lst2) (length ap) eq) in
                               let eq3 = the ((length (ap ++ lst2)) = ((length ap) + (length lst1))) (rewrite eq0 in eq2) in
                               rewrite eq3 in eq1

lengthPreserved : (list1 : List Nat) -> (list2 : List Nat) -> (Same list1 list2) -> ((length list1) = (length list2))
lengthPreserved l1 l2 prf = case prf of
                              Nils => Refl
                              Append h t1 t2 tPrf => let tailsEq = the ((length t1) = (length t2)) (lengthPreserved t1 t2 tPrf) in
                                rewrite tailsEq in Refl
                              Swap beg x1 mid x2 end =>
                                 let step1 = the ( (length ((x1 :: end))) = (length ((x2 :: end))) ) Refl in
                                 let step2 = the ( (length (mid ++ (x1 :: end))) = (length (mid ++ (x2 :: end))) ) (lengthLemma (x1 :: end) (x2 :: end) step1) in
                                 let step3 = the ( (length (x2 :: (mid ++ (x1 :: end)))) = (length (x1 :: (mid ++ (x2 :: end)))) ) (rewrite step2 in Refl) in
                                 let step4 = the (length (beg ++ x2 :: mid ++ x1 :: end) = length (beg ++ x1 :: mid ++ x2 :: end)) $ lengthLemma{ap = beg} (x2 :: (mid ++ (x1 :: end))) (x1 :: (mid ++ (x2 :: end))) step3 in
                                 rewrite step4 in Refl
                              Trans{l2 = r} s1 s2 => let eq1 = the ((length l1) = (length r)) (lengthPreserved l1 r s1) in
                                                     let eq2 = the ((length r) = (length l2)) (lengthPreserved r l2 s2) in
                                                     rewrite eq1 in eq2


nilIsNotSameToCons: (h : Nat) -> (t : List Nat) -> (Same (h::t) Nil) -> Void
nilIsNotSameToCons hd tl prf = let x = lengthPreserved (hd :: tl) Nil prf in absurd x

symSame: Same lst1 lst2 -> Same lst2 lst1
symSame prf = case prf of
                Nils => Nils
                Append h l1 l2 prf1  => Append h l2 l1 (symSame prf1)
                Swap beg x1 mid x2 end => Swap beg x2 mid x1 end
                Trans s1 s2 => Trans (symSame s2) (symSame s1)


reflSame: (l: List Nat) -> Same l l
reflSame [] = Nils
reflSame (x :: xs) = Append x xs xs (reflSame xs)

data Sorted: (l: List Nat) -> Type where
  Empty: Sorted Nil
  Singletone: (a: Nat) -> Sorted [a]
  Prepend: (a : Nat) -> (tail : List Nat) -> (LTE a b) -> (s: Sorted (b :: tail)) -> Sorted (a :: b:: tail)

tailOfSortedIsSorted: Sorted (x :: xs) -> Sorted xs
tailOfSortedIsSorted{x}{xs} pr = case pr of
                                      Empty impossible
                                      (Singletone y) => Empty
                                      Prepend x xs _ prf => prf


data SortResult: (source: List Nat) -> (res : List Nat) -> Type where
  MkRes: (Same source0 res0) -> (Sorted res0)  -> SortResult source0 res0

SortResultEx : (l : List Nat) -> Type
SortResultEx l = Exists (\r => SortResult l r)

SortResultEx2 : (h : Nat) -> (l : List Nat) -> Type
SortResultEx2 h l = Exists (\t => SortResult l (h :: t))

extract : (SortResultEx l) -> (List Nat)
extract (Evidence a b) = a

nilIsNorASortResultOfCons:  (h : Nat) -> (tail : List Nat) -> (SortResult (h :: tail) Nil) -> Void
nilIsNorASortResultOfCons hd tl (MkRes same _) = nilIsNotSameToCons hd tl same


appendSmaller: (next : Nat) -> (resHead : Nat) -> LTE next resHead-> (resTail: List Nat) -> SortResult (resHead :: resTail)  (resHead :: resTail) -> SortResultEx (next :: resHead :: resTail)
appendSmaller n resH lte resT prf = case prf of
                                             MkRes tailSame tailSorted =>
                                                          let resSorted = the (Sorted (n :: resH :: resT)) (Prepend{b=resH} n resT lte tailSorted)  in
                                                          let same = the (Same (n ::resH :: resT) (n :: resH :: resT)) (Append n (resH :: resT) (resH :: resT) tailSame)  in
                                                          Evidence (n :: resH :: resT) (MkRes same resSorted)

tailOfSortResIsSorted: SortResult (h::tl) (h::tl) -> SortResult tl tl
tailOfSortResIsSorted{h}{tl} (MkRes same sorted) =
                                              let tSorted = the (Sorted tl) (tailOfSortedIsSorted sorted) in
                                              let tSame = reflSame tl in
                                              MkRes tSame tSorted

firstSmallerThanSecondInSorted: (r1 : Nat) -> (r2 : Nat) -> (t : List Nat) -> Sorted (r1 :: r2 :: t) -> LTE r1 r2
firstSmallerThanSecondInSorted x y tl prf = case prf of
                                                Empty impossible
                                                Singletone _ impossible
                                                Prepend x _ lte _ => lte

sortReordered : (source1 : List Nat) -> (source2 : List Nat) -> (result : List Nat) -> Same source1 source2 -> SortResult source1 result -> SortResult source2 result
sortReordered s1 s2 res same12 (MkRes same1r sorted)= let same2r = Trans (symSame same12) same1r in MkRes same2r sorted

sortIsIdempotent : (source : List Nat) -> (result : List Nat) -> SortResult source result -> SortResult result result
sortIsIdempotent src res r@(MkRes same sorted) = sortReordered src res res same r

sortReorderedEx : (source1 : List Nat) -> (source2 : List Nat) -> Same source1 source2 -> SortResultEx source1 -> SortResultEx source2
sortReorderedEx s1 s2 same (Evidence r prf) = Evidence r (sortReordered s1 s2 r same prf)



insertIntoSingletone: (x : Nat) -> (y : Nat) -> SortResultEx [x,y]
insertIntoSingletone a b = case (order{to = LTE} a b) of
                              Left aIsSmaller =>  let sorted = Prepend a [] aIsSmaller (Singletone b) in
                                                  let same = reflSame [a, b] in
                                                  Evidence [a,b] (MkRes same sorted)
                              Right bIsSmaller => let sorted = Prepend b [] bIsSmaller (Singletone a) in
                                                  let same = Swap [] a [] b [] in
                                                  Evidence [b,a] (MkRes same sorted)

mutual
  insertSmall : (e : Nat) -> (h : Nat) -> (t : List Nat) -> (LTE e h) -> (Sorted (h :: t)) -> SortResultEx2 e (e :: h :: t)
  insertSmall v x xs lte srt = let same = reflSame (v :: x :: xs) in
                               let sorted = the (Sorted (v::x::xs)) (Prepend{b=x} v xs lte srt) in
                               Evidence (x :: xs) (MkRes same sorted)

  insertBig : (e : Nat) -> (h : Nat) -> (t : List Nat) -> (LTE h e) -> (Sorted (h :: t)) -> SortResultEx2 h (e :: h :: t)
  insertBig v x1 Nil lte srt = let sorted = the (Sorted [x1, v]) (Prepend{b=v} x1 Nil lte (Singletone v)) in
                               let same = the (Same [v, x1] [x1, v]) (Swap [] v [] x1 []) in
                               Evidence [v] (MkRes same sorted)
  insertBig v x1 (x2 :: xs) lte srt = case (order{to = LTE} v x2) of
                                        Left vIsSmall => let (Evidence resT (MkRes same sorted)) = insertSmall v x2 xs vIsSmall (tailOfSortedIsSorted srt) in
                                                         let sorted1 = the (Sorted (x1 :: v :: resT) ) (Prepend{b=v} x1 resT lte sorted) in
                                                         let same1 = the (Same (v :: x2 :: xs) (v :: resT) ) same in
                                                         let same2 = the (Same (x1 :: v :: x2 :: xs) (x1 :: v :: resT) ) (Append x1 (v :: x2 :: xs) (v :: resT) same1) in
                                                         let same3 = the (Same (v :: x1 :: x2 :: xs) (x1 :: v :: x2 :: xs)) (Swap [] v [] x1 (x2 :: xs)) in
                                                         let same4 = the (Same (v :: x1 :: x2 :: xs) (x1 :: v :: resT)) (Trans same3 same2) in
                                                         let final = the (SortResult (v :: x1 :: x2 :: xs) (x1 :: v :: resT)) (MkRes same4 sorted1) in
                                                         Evidence (v :: resT) final
                                        Right vIsBig =>  let (Evidence resT (MkRes same sorted)) = insertBig v x2 xs vIsBig (tailOfSortedIsSorted srt) in
                                                         let x1LTx2 = firstSmallerThanSecondInSorted x1 x2 xs srt in
                                                         let sorted1 = the (Sorted (x1 :: x2 :: resT) ) (Prepend{b=x2} x1 resT x1LTx2 sorted) in
                                                         let same1 = the (Same (v :: x2 :: xs) (x2 :: resT) ) same in
                                                         let same2 = the (Same (x1 :: v :: x2 :: xs) (x1 :: x2 :: resT) ) (Append x1 (v :: x2 :: xs) (x2 :: resT) same1) in
                                                         let same3 = the (Same (v :: x1 :: x2 :: xs) (x1 :: v ::  x2 :: xs)) (Swap [] v [] x1 (x2 :: xs)) in
                                                         let same4 = the (Same (v :: x1 :: x2 :: xs) (x1 :: x2 :: resT))  (Trans same3 same2) in
                                                         let final = the (SortResult (v :: x1 :: x2 :: xs) (x1 :: x2 :: resT)) (MkRes same4 sorted1) in
                                                         Evidence (x2 :: resT) final

insertionSort: (l: List Nat) ->  SortResultEx l
insertionSort [] = Evidence [] (MkRes Nils Empty)
insertionSort (x :: xs) =  let (Evidence res (MkRes same sorted)) = insertionSort xs in
                           case res of
                             Nil => case xs of
                                      Nil => Evidence [x] (MkRes (reflSame [x]) (Singletone x))
                                      xs1 :: xss => absurd (nilIsNotSameToCons xs1 xss same)
                             r :: rs =>
                                let eq = the (res = (r::rs)) ?eqqqqqq in
                                let sameHint = the (Same res (r::rs) ) (rewrite eq in (reflSame (r::rs))) in
                                case (order{to = LTE} x r) of
                                     Left xSmall => let (Evidence tRes prf) = insertSmall x r rs xSmall sorted in
                                                    case prf of
                                                      MkRes same1 sorted1 =>
                                                        let same11 = the (Same (x :: r :: rs) (x :: tRes)) same1 in
                                                        let same0 = the (Same xs (r :: rs) ) same in
                                                        let same00 = the (Same (x :: xs) (x :: r :: rs) ) (Append x xs (r :: rs) same0) in
                                                        let same5 = the (Same (x :: xs) (x :: tRes) ) (Trans same00 same1) in
                                                        Evidence (x :: tRes) (MkRes same5 sorted1)
                                     Right x1Big => let (Evidence tRes prf) = insertBig x r rs x1Big sorted in
                                                    case prf of
                                                      MkRes same1 sorted1 =>
                                                        let same11 = the (Same (x :: r :: rs) (r :: tRes)) same1 in
                                                        let same0 = the (Same xs (r :: rs) ) same in
                                                        let same00 = the (Same xs res ) (rewrite eq in same0) in
                                                        let same000 = the (Same (x :: res) (x :: r :: rs) ) (Append x res (r :: rs) sameHint) in
                                                        let same2 = the (Same (x :: res) (r :: tRes) ) (Trans same000 same11) in
                                                        let same3 = the (Same (x :: xs) (x :: res) ) (Append x xs res same00) in
                                                        let same5 = the (Same (x :: xs) (r :: tRes) ) (Trans same3 same2) in
                                                        Evidence (r :: tRes) (MkRes same5 sorted1)
