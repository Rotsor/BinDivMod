module CntTest where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as PE using
                                                        (_≡_; cong; refl)
open PE.≡-Reasoning
open import Data.Empty using (⊥-elim)
open import Data.List  using (List; []; _∷_; [_])
open import Data.Nat   using (ℕ; suc) renaming (pred to predN)

open import Foreign.Haskell
open import IO.Primitive
open import Data.String using (String; toCostring)

-- of applcation ---
open import List0 using (concatStr)  
open import Bin0  using (Bin; toℕ; pred) renaming (show to showB)  
open import Bin2  using (toℕ-pred-homo; toℕ-bs1≢0)  



--****************************************************************************
open Bin

downFrom : Bin → List Bin
downFrom x =
           aux x (toℕ x) refl
  where
  aux :  (x : Bin) → (cnt : ℕ) → toℕ x ≡ cnt → List Bin
  aux 0#      _         _         =  [ 0# ]
  aux (bs 1#) 0         bs1N≡0    =  ⊥-elim (toℕ-bs1≢0 bs bs1N≡0)  
  aux (bs 1#) (suc cnt) bs1N≡cnt' =  bs1 ∷ (aux (pred bs1) cnt eq)
                   where
                   bs1 = bs 1#

                   eq :  toℕ (pred bs1) ≡ cnt 
                   eq =  begin toℕ (pred bs1)   ≡⟨ toℕ-pred-homo bs1 ⟩
                               predN (toℕ bs1)  ≡⟨ cong predN bs1N≡cnt' ⟩
                               predN (suc cnt)  ≡⟨ refl ⟩
                               cnt
                         ∎ 

last :  Bin → List Bin → Bin
last x []       =  x 
last _ (x ∷ xs) =  last x xs 

test :  Bin → List String  
test x =
       "x = "     ∷ showB x   ∷   
       "\nxL = "  ∷ showB xL  ∷
       []
       where
       xs = downFrom x;  xL = last 0# xs


main = (readFiniteFile "data.txt") >>= putStrLn ∘ toCostring ∘ g
       where
       g : String -> String
       g str = concatStr (test a)  where
                                   a : Bin
                                   a = Bin0.fromString str

-- Time cost:  test n  costs  O(n).


