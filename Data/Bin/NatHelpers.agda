module Data.Bin.NatHelpers where

    open import Relation.Binary.PropositionalEquality
    open import Data.Empty
    open import Data.Fin using (Fin; zero; suc) renaming (toℕ to finToℕ)
    open import Data.Nat using(ℕ; zero; suc; _≤_; _+_; _*_; s≤s; z≤n; ≤′-step; ≤′-refl; _<_; _∸_)
    open import Data.Nat.Properties using(_*-mono_; ≤′⇒≤; ≤⇒≤′)
    open import Function using (_∘_)
    open import Relation.Nullary


    ≤-step : ∀ {a b} → a ≤ b → a ≤ suc b
    ≤-step = ≤′⇒≤ ∘ ≤′-step ∘ ≤⇒≤′

    *2-mono : ∀ x → x ≤ x * 2
    *2-mono zero = z≤n
    *2-mono (suc x) = s≤s (≤-step (*2-mono x))

    kojojo : ∀ (b : Fin 2) x → x ≢ 0 → suc x ≤ finToℕ b + x * 2
    kojojo b zero nz = ⊥-elim (nz refl)
    kojojo zero (suc y) nz = s≤s (s≤s (*2-mono y))
    kojojo (suc zero) (suc y) nz = s≤s (s≤s (≤-step (*2-mono y)))
    kojojo (suc (suc ())) (suc y) nz

    *2-gives-space : ∀ {x y z} → (x < y) → z < 2 → x * 2 + z < y * 2
    *2-gives-space {suc x} {suc (suc y)} (s≤s (s≤s less)) zz = s≤s (s≤s (*2-gives-space {x} {suc y} (s≤s less) zz))
    *2-gives-space (s≤s z≤n) (s≤s (s≤s z≤n)) = s≤s (s≤s z≤n)
    *2-gives-space (s≤s z≤n) (s≤s z≤n) = s≤s z≤n

    open import Data.Product

    x≮z→x≡z+y : ∀ {x z} → ¬ x < z → ∃ λ y → x ≡ z + y
    x≮z→x≡z+y {zero} {zero} x≮z = zero , refl
    x≮z→x≡z+y {suc x} {zero} x≮z = suc x , refl
    x≮z→x≡z+y {zero} {suc z} x≮z = ⊥-elim (x≮z (s≤s z≤n))
    x≮z→x≡z+y {suc x} {suc z} x≮z with x≮z→x≡z+y {x} {z} (λ z' → x≮z (s≤s z'))
    x≮z→x≡z+y {suc .(z + y)} {suc z} x≮z | y , refl = y , refl

    +-elim₁ : ∀ {x y z} → z + x < z + y → x < y
    +-elim₁ {x} {y} {zero} lt = lt
    +-elim₁ {x} {y} {suc z} (s≤s lt) = +-elim₁ {x} {y} {z} lt

    import Data.Nat.Properties
    open import Algebra.Structures
    open IsCommutativeSemiring (Data.Nat.Properties.isCommutativeSemiring)

    +-elim₂ : ∀ {x y z} → x + z < y + z → x < y
    +-elim₂ {x} {y} {z} lt rewrite +-comm x z | +-comm y z = +-elim₁ {x} {y} {z} lt