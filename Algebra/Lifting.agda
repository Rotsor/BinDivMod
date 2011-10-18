import Algebra
import Algebra.Structures
import Function.Equality
import Function.Equivalence
import Function.Bijection
import Level
import Relation.Binary
import Algebra.FunctionProperties
import Relation.Binary.EqReasoning

open Level renaming (zero to ₀)
open Relation.Binary using (Setoid; module Setoid)
open Function.Bijection

module Algebra.Lifting
  (S₁ S₂ : Setoid ₀ ₀)
  (f : Bijection S₁ S₂) where

  open Algebra.FunctionProperties using (Op₂; LeftIdentity)
  open Algebra.Structures

  open Setoid S₁ using () renaming (Carrier to A₁; _≈_ to _≈₁_; sym to sym₁; refl to refl₁; trans to trans₁)
  open Setoid S₂ using (sym; trans) renaming (Carrier to A₂; _≈_ to _≈₂_; isEquivalence to isEquivalence₂)
  open Bijection f
  open Function.Equality using (_⟨$⟩_; cong)
  module WithOp₂
   (_+₁_ : Op₂ A₁)
   (_+₂_ : Op₂ A₂)
   (+-same : ∀ x y → from ⟨$⟩ (x +₂ y) ≈₁ (from ⟨$⟩ x) +₁ (from ⟨$⟩ y)) where

   open Relation.Binary.EqReasoning S₁ renaming (begin_ to begin₁_; _∎ to _∎₁; _≈⟨_⟩_ to _≈₁⟨_⟩_)
   open Relation.Binary.EqReasoning S₂ renaming (begin_ to begin₂_; _∎ to _∎₂; _≈⟨_⟩_ to _≈₂⟨_⟩_)

   open import Function using (_⟨_⟩_)

   from-inj : ∀ {x y} → from ⟨$⟩ x ≈₁ from ⟨$⟩ y → x ≈₂ y
   from-inj {x} {y} eq = (sym (right-inverse-of x)) ⟨ trans ⟩ cong to eq ⟨ trans ⟩ (right-inverse-of y)


   lift-comm : (∀ x y → (x +₁ y) ≈₁ (y +₁ x)) → (∀ x y → (x +₂ y) ≈₂ (y +₂ x)) 
   lift-comm comm₁ x y = from-inj (
       begin₁
          from ⟨$⟩ x +₂ y
           ≈₁⟨ +-same x y ⟩
          (from ⟨$⟩ x) +₁ (from ⟨$⟩ y)
           ≈₁⟨ comm₁ (from ⟨$⟩ x) (from ⟨$⟩ y) ⟩
          (from ⟨$⟩ y) +₁ (from ⟨$⟩ x)
           ≈₁⟨ sym₁ (+-same y x) ⟩
          from ⟨$⟩ y +₂ x
       ∎₁
      )

   using-+-same : ∀ {a b c d}
                  → (from ⟨$⟩ a) +₁ (from ⟨$⟩ b) ≈₁ (from ⟨$⟩ c) +₁ (from ⟨$⟩ d)
                  → from ⟨$⟩ a +₂ b ≈₁ from ⟨$⟩ c +₂ d
   using-+-same {a} {b} {c} {d} eq =
    begin₁
     from ⟨$⟩ a +₂ b
      ≈₁⟨ +-same a b ⟩
     (from ⟨$⟩ a) +₁ (from ⟨$⟩ b)
      ≈₁⟨ eq ⟩
     (from ⟨$⟩ c) +₁ (from ⟨$⟩ d)
      ≈₁⟨ sym₁ (+-same c d) ⟩
     from ⟨$⟩ c +₂ d
    ∎₁

   lift-comm' : (∀ x y → (x +₁ y) ≈₁ (y +₁ x)) → (∀ x y → (x +₂ y) ≈₂ (y +₂ x)) 
   lift-comm' comm₁ x y = from-inj (using-+-same (comm₁ (from ⟨$⟩ x) (from ⟨$⟩ y)))

   lift-assoc : (∀ x y z → (x +₁ y) +₁ z ≈₁ x +₁ (y +₁ z)) 
              → (∀ {a b c d} → a ≈₁ b → c ≈₁ d → a +₁ c ≈₁ b +₁ d)
              → (∀ x y z → (x +₂ y) +₂ z ≈₂ x +₂ (y +₂ z))
   lift-assoc assoc₁ +₁-cong x y z = from-inj (using-+-same (
    begin₁
      (from ⟨$⟩ x +₂ y) +₁ fz
       ≈₁⟨ +₁-cong (+-same x y) refl₁ ⟩
      (fx +₁ fy) +₁ fz
       ≈₁⟨ assoc₁ fx fy fz ⟩
      fx +₁ (fy +₁ fz)
       ≈₁⟨ +₁-cong  refl₁ (sym₁ (+-same y z)) ⟩
      fx +₁ (from ⟨$⟩ y +₂ z)
    ∎₁)) where
     fx = from ⟨$⟩ x
     fy = from ⟨$⟩ y
     fz = from ⟨$⟩ z

   +Cong₁ = (∀ {a b c d} → a ≈₁ b → c ≈₁ d → a +₁ c ≈₁ b +₁ d)
   +Cong₂ = (∀ {a b c d} → a ≈₂ b → c ≈₂ d → a +₂ c ≈₂ b +₂ d)

   lift-cong : +Cong₁ → +Cong₂
   lift-cong cong₁ a≈₂b c≈₂d = from-inj (using-+-same (cong₁ (cong from  a≈₂b) (cong from  c≈₂d)))

   lift-isSemigroup : IsSemigroup _≈₁_ _+₁_ → IsSemigroup _≈₂_ _+₂_ 
   lift-isSemigroup isSemigroup = record 
     { isEquivalence = isEquivalence₂
     ; assoc = lift-assoc assoc ∙-cong
     ; ∙-cong = lift-cong ∙-cong
     } where
    open IsSemigroup isSemigroup

   lift-LeftIdentity : ∀ ε → +Cong₁ → LeftIdentity _≈₁_ ε _+₁_ → LeftIdentity _≈₂_ (to ⟨$⟩ ε) _+₂_
   lift-LeftIdentity ε +-cong₁ identityˡ x = from-inj (
    begin₁
     from ⟨$⟩ (to ⟨$⟩ ε) +₂ x
      ≈₁⟨ +-same (to ⟨$⟩ ε) x ⟩
     (from ⟨$⟩ (to ⟨$⟩ ε)) +₁ (from ⟨$⟩ x)
      ≈₁⟨ +-cong₁ (left-inverse-of ε) refl₁ ⟩
     ε +₁ (from ⟨$⟩ x)
      ≈₁⟨ identityˡ (from ⟨$⟩ x) ⟩
     from ⟨$⟩ x
    ∎₁)

   lift-isCommutativeMonoid : ∀ ε → IsCommutativeMonoid _≈₁_ _+₁_ ε → IsCommutativeMonoid _≈₂_ _+₂_ (to ⟨$⟩ ε)
   lift-isCommutativeMonoid ε isCommMonoid = record 
     { isSemigroup = lift-isSemigroup isSemigroup
     ; identityˡ = lift-LeftIdentity ε ∙-cong identityˡ
     ; comm = lift-comm comm
     } where
    open IsCommutativeMonoid isCommMonoid
