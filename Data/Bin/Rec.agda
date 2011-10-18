module Data.Bin.Rec where

open import Data.Bin hiding (suc)
open import Induction.WellFounded

open import Data.Nat using (ℕ; zero; suc) renaming (_<′_ to _ℕ<_)
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality
open import Data.Bin.Bijection

import Induction.Nat

wf : Well-founded _<_
wf x = go' x where
  P : ℕ → Set
  P x = Acc _<_ (fromℕ x)

  podgon : ∀ {y} → P (toℕ y) → Acc _<_ y
  podgon = subst (λ q → Acc _<_ q) (fromToℕ-inverse _)

  go'' : (x : ℕ) → ((y : ℕ) → y ℕ< x → P y) → P x
  go'' x rec = acc (λ { y (less ty<tfx) → podgon (rec (toℕ y) (subst (λ q → toℕ y ℕ< q) (toFromℕ-inverse x) (≤⇒≤′ ty<tfx) ) )})

  go : (x : ℕ) → P x
  go = Induction.Nat.<-rec P go''

  go' : (x : Bin) → Acc _<_ x
  go' x = podgon (go (toℕ x))


open All wf

rec : ∀ (P : Bin → Set) → ((a : Bin) → ((a' : Bin) → (a' < a) → P a') → P a) → (a : Bin) → P a
rec P f = wfRec P f