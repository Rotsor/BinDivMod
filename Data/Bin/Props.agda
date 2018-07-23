module Data.Bin.Props where

  open import Data.Bin
  import Data.Nat
  import Data.Nat.Properties
  open Data.Nat using (ℕ)
  open import Data.List
  open import Relation.Binary.PropositionalEquality
  open import Function using (_⟨_⟩_)
  open import Algebra.Structures using (IsCommutativeMonoid; module IsCommutativeMonoid; module IsCommutativeSemiring)

  import Data.Bin.Addition

  bin-+-is-comm-monoid = Data.Bin.Addition.is-commutativeMonoid

  open import Data.Bin.Bijection using (fromℕ-bijection)

  import Algebra.Lifting
  module Lifting = Algebra.Lifting _ _ fromℕ-bijection

  open import Data.Bin.Multiplication

  bin-*-is-comm-monoid : IsCommutativeMonoid _≡_ _*_ ([] 1#)
  bin-*-is-comm-monoid = lift-isCommutativeMonoid 1 *-isCommutativeMonoid
   where
     open IsCommutativeSemiring Data.Nat.Properties.isCommutativeSemiring using(*-isCommutativeMonoid)
     open Lifting.WithOp₂ Data.Nat._*_ _*_ *-is-multiplication

  open IsCommutativeMonoid bin-*-is-comm-monoid using () renaming (comm to *-comm)

  *2-is-2* : ∀ x → x *2 ≡ (fromℕ 2) * x
  *2-is-2* 0# = refl
  *2-is-2* (bs 1#) = refl

  *-distrib : ∀ {a b c} → (a + b) * c ≡ a * c + b * c
  *-distrib {a} {b} {c} = Data.Bin.Multiplication.*-distribʳ a b c

  *2-distrib : ∀ a b → (a + b) *2 ≡ a *2 + b *2
  *2-distrib a b = *2-is-*2-bin (a + b) ⟨ trans ⟩ *-distrib {a} {b} {fromℕ 2} ⟨ trans ⟩ cong₂ _+_ (sym (*2-is-*2-bin a)) (sym (*2-is-*2-bin b))
   where
    *2-is-*2-bin : ∀ a → a *2 ≡ a * fromℕ 2
    *2-is-*2-bin a = *2-is-2* a ⟨ trans ⟩ *-comm (fromℕ 2) a
