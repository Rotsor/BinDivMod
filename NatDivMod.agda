module NatDivMod where

open import Function         using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary  using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality as PE using 
                                                     (_≡_; refl; trans; cong)
open PE.≡-Reasoning
open import Data.Empty      using (⊥-elim)
open import Data.Sum        using (_⊎_; inj₁; inj₂)
open import Data.Nat        using (_≟_; suc; _+_; _*_; ⌊_/2⌋)
open import Data.Nat.DivMod using (DivMod; _divMod_; _div_)
open import NatProp0        using (≤1→0or1; half<n*2>; half<1+n*2>)
open import Data.Fin as Fin using (toℕ)
import Data.Fin.Properties as FinP


-- Equivalence of the two ways of division by 2 ---------------------------

half-n=n-div-2 :  ∀ n → ⌊ n /2⌋ ≡ (n div 2)
half-n=n-div-2 n =
  case
      rN ≟ 0
  of \
  { (yes rN=0) → let n=q*2 : n ≡ q * 2
                     n=q*2 = trans n=rN+q*2 (cong (_+ (q * 2)) rN=0)
                 in
                 begin  ⌊ n /2⌋         ≡⟨ cong ⌊_/2⌋ n=q*2 ⟩
                        ⌊ (q * 2) /2⌋   ≡⟨ half<n*2> q ⟩
                        q               ≡⟨ q=n-div-2 ⟩
                        n div 2
                 ∎
  ; (no rN/=0) →
            let  rN=1 : rN ≡ 1
                 rN=1 = case rN=0or1 of \ { (inj₁ rN=0) → ⊥-elim (rN/=0 rN=0)
                                          ; (inj₂ rN=1) → rN=1
                                          }
                 n=1+q*2 : n ≡ suc (q * 2)
                 n=1+q*2 = begin  n              ≡⟨ n=rN+q*2 ⟩
                                  rN + (q * 2)   ≡⟨ cong (_+ (q * 2)) rN=1 ⟩
                                  1 + (q * 2)
                           ∎
            in
            begin  ⌊ n /2⌋               ≡⟨ cong ⌊_/2⌋ n=1+q*2 ⟩
                   ⌊ (suc (q * 2)) /2⌋   ≡⟨ half<1+n*2> q ⟩
                   q                     ≡⟨ q=n-div-2 ⟩
                   n div 2
            ∎
  }
  where
  open DivMod
  res      = n divMod 2
  q        = quotient  res
  r        = remainder res
  rN       = toℕ r
  n=rN+q*2 = property res

  q=n-div-2 : q ≡ (n div 2)
  q=n-div-2 = refl

  rN≤1 = FinP.prop-toℕ-≤ {2} r

  rN=0or1 :  rN ≡ 0 ⊎ rN ≡ 1
  rN=0or1 =  ≤1→0or1 rN rN≤1

