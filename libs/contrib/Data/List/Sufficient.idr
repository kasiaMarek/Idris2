||| 'Sufficient' lists: a structurally inductive view of lists xs
||| as given by xs = non-empty prefix + sufficient suffix
|||
||| Useful for termination arguments for function definitions
||| which provably consume a non-empty (but otherwise arbitrary) prefix
||| *without* having to resort to ancillary WF induction on length etc.
||| e.g. lexers, parsers etc.
|||
||| Credited by Conor McBride as originally due to James McKinna
module Data.List.Sufficient

import Control.WellFounded

%default total

public export
data Suffix : (ys,xs : List a) -> Type where
  IsSuffix : (x : a) -> (zs : List a)
          -> (0 ford : xs = x :: zs ++ ys) -> Suffix ys xs

SuffixAccessible : (xs : List a) -> Accessible Suffix xs
SuffixAccessible [] = Access (\y => \case (IsSuffix x zs _) impossible)
SuffixAccessible ws@(x :: xs) =
  let fact1@(Access f) = SuffixAccessible xs
  in Access $ \ys => \case
    (IsSuffix x [] Refl) => fact1
    (IsSuffix x (z :: zs) Refl) => f ys (IsSuffix z zs Refl)

public export
WellFounded (List a) Suffix where
  wellFounded = SuffixAccessible

public export
SuffAcc : (a : Type) -> (p : List a -> Type) -> (xs : List a) -> Type
SuffAcc a p xs = {x : _} -> (pre : _) -> (suffix : _) -> (xs = x :: pre ++ suffix) -> p suffix

public export
SuffRec : (a : Type) -> (p : List a -> Type) -> (ys : List a) -> Type
SuffRec a p ys = (ih : SuffAcc a p ys) -> p ys

public export
SuffCovered : (a : Type)-> (p : List a -> Type)
            -> (rp : (xs : List a) -> p xs -> Type) 
            -> (xs : List a) -> (suf : SuffAcc a p xs) -> Type

SuffCovered a p rp xs suf =
  {x : _} -> {pre : _} -> (suffix : _) ->
  (eq : xs = x :: pre ++ suffix) -> rp suffix (suf pre suffix eq)

parameters (A : Type) (B : List A -> Type) (rec : (ys : List A) -> SuffRec A B ys)
  suffRec : (zs : List A) -> B zs
  suffRec = wfInd {a = List A, rel = Suffix} $ \xs,rec' =>
    rec xs (\pre,ys,ford => rec' ys $ IsSuffix _ _ ford)

  parameters (C : (xs : List A) -> B xs -> Type)
             (ih : (xs : List A) -> (suf : SuffAcc A B xs)
                 -> SuffCovered A B C xs suf -> C xs (rec xs suf))
    suffInd : (xs : List A) -> C xs (suffRec xs)
    suffInd xs =
      wfIndProp {a = List A, rel = Suffix, P = B, RP = C} _
        (\xs,rec',ih' => ih xs _ (\suff,Refl => ih' suff (IsSuffix _ _ Refl)))
        xs