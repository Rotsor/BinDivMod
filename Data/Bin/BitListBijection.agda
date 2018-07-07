{-# OPTIONS --termination-depth=10 #-}
module Data.Bin.BitListBijection where

--
-- This module gives a bijection between the two setoids:
-- - the set (ℕ)
-- - The set (List Bit), interpreted as least-significant-bit first,
--   with the equivalence relation that ignores the zeroes at the end of the list

  open import Data.List
  open import Data.List.Properties
  import Data.Digit
  open Data.Digit using (Bit)
  open import Data.Fin using (zero; suc; Fin; inject₁) renaming (toℕ to finToℕ)
  open import Data.Nat using (ℕ; zero;suc)
  open import Data.Nat using (_+_)
  open import Data.Nat.Properties using (+-suc; +-identityʳ) renaming (suc-injective to suc-inj)
  open import Data.Fin.Properties using () renaming (suc-injective to fin-suc-inj)


  infix 3 _≈_ _≈ʳ_

  0×_ : ℕ → List Bit
  0× n = replicate n zero

  data _≈_ : List Bit → List Bit → Set where
    equiv : ∀ l n m → l ++ 0× n ≈ l ++ 0× m

  data _≈ʳ_ : List Bit → List Bit → Set where
    equiv : ∀ n m l → 0× n ++ l ≈ʳ 0× m ++ l

  open import Relation.Binary using (IsEquivalence; Setoid; Reflexive; Symmetric; Transitive)
  import Relation.Binary.PropositionalEquality
  module PropEq = Relation.Binary.PropositionalEquality
  open import Algebra
  import Level

  open import Algebra.FunctionProperties
  open import Data.Product renaming (map to pmap)
  
  ₀ = Level.zero

  open PropEq using (_≡_)

  []-identityʳ : ∀ l → l ++ [] ≡ l
  []-identityʳ = proj₂ (Monoid.identity (Data.List.Properties.++-monoid Bit))

  ≈-sym : Symmetric _≈_
  ≈-sym (equiv l n m) = equiv l m n

  equivˡ : ∀ n l → l ++ 0× n ≈ l
  equivˡ n l = PropEq.subst ( λ x → l ++ 0× n ≈ x) ([]-identityʳ l) (equiv l n 0)

  ≈-refl : Reflexive _≈_
  ≈-refl {x} =  PropEq.subst (λ x → x ≈ x) ([]-identityʳ x) (equiv x 0 0) 

  patternMatch : ∀ {A : Set} (P : A → Set) {x} → P x → ∃ λ z → P z × x ≡ z
  patternMatch _ {x = x} px = (x , (px , PropEq.refl))

  generalizing_case_of_ : ∀ {a b} {A : Set a} {B : Set b} → (P : A → Set) → ∀ {x} → P x → (∀ {z} → P z → x ≡ z → B) → B
  generalizing P case p of f = f p PropEq.refl

  open import Data.Sum

  ≡→≈ : ∀ {x y} → x ≡ y → x ≈ y
  ≡→≈ {x} .{x} PropEq.refl = ≈-refl {x}

  open import Function

  open import Data.Digit

  data All-zero : List Bit → Set where
    [] : All-zero []
    cons : ∀ {t} → All-zero t → All-zero (0b ∷ t)

  -- ᵢ for "Inductive"
  data _≈ᵢ_ : List Bit → List Bit → Set where
    both-zero : ∀ {a b} (a-zero : All-zero a) (b-zero : All-zero b) → a ≈ᵢ b
    heads-match : ∀ h at bt → at ≈ᵢ bt → (h ∷ at) ≈ᵢ (h ∷ bt)

  All-zero-respects-equivalence : ∀ {x y} → x ≈ᵢ y → All-zero x → All-zero y
  All-zero-respects-equivalence (both-zero a-zero b-zero) z = b-zero
  All-zero-respects-equivalence (heads-match .zero at bt eq) (cons z) = cons (All-zero-respects-equivalence eq z)

  ≈ᵢ-sym : ∀ {a b} → a ≈ᵢ b → b ≈ᵢ a
  ≈ᵢ-sym (both-zero a-zero b-zero) = both-zero b-zero a-zero
  ≈ᵢ-sym (heads-match h at bt l) = heads-match h bt at (≈ᵢ-sym l)

  ≈ᵢ-trans : ∀ {a b c} → a ≈ᵢ b → b ≈ᵢ c → a ≈ᵢ c
  ≈ᵢ-trans (both-zero a-zero b-zero) b≈c = both-zero a-zero (All-zero-respects-equivalence b≈c b-zero) 
  ≈ᵢ-trans a≈b (both-zero b-zero c-zero) = both-zero (All-zero-respects-equivalence (≈ᵢ-sym a≈b) b-zero) c-zero
  ≈ᵢ-trans (heads-match h at bt r1) (heads-match .h .bt bt₁ r2) = heads-match h _ _ (≈ᵢ-trans r1 r2) 

  0×-is-all-zero : ∀ {n} → All-zero (0× n)
  0×-is-all-zero {ℕ.zero} = []
  0×-is-all-zero {ℕ.suc n} = cons 0×-is-all-zero

  ≈-to-ᵢ : ∀ {a b} → a ≈ b → a ≈ᵢ b
  ≈-to-ᵢ (equiv [] n m) = both-zero 0×-is-all-zero 0×-is-all-zero
  ≈-to-ᵢ (equiv (x ∷ l) n m) = heads-match _ _ _ (≈-to-ᵢ (equiv l n m))

  az-replicate : ∀ {a} → All-zero a → (0× length a) ≡ a
  az-replicate [] = PropEq.refl
  az-replicate (cons x) = PropEq.cong (λ z → 0b ∷ z) (az-replicate x)

  ᵢ-to-≈ : ∀ {a b} → a ≈ᵢ b → a ≈ b
  ᵢ-to-≈ (both-zero {a} {b} a-zero b-zero) =
     PropEq.subst₂ _≈_ (az-replicate a-zero) (az-replicate b-zero) (equiv [] (length a) (length b))
  ᵢ-to-≈ (heads-match h at bt e) =
    case ᵢ-to-≈ e of λ { (equiv l n m) → equiv (h ∷ l) n m }

  ≈-trans : Transitive _≈_
  ≈-trans = λ a b → ᵢ-to-≈ (≈ᵢ-trans (≈-to-ᵢ a) (≈-to-ᵢ b))

  isEquivalence : IsEquivalence _≈_
  isEquivalence = record
    { refl = ≈-refl
    ; trans = ≈-trans
    ; sym = ≈-sym
    }

  setoid : Setoid ₀ ₀
  setoid = record {isEquivalence = isEquivalence}

  toℕ : List Bit → ℕ
  toℕ = fromDigits

  open import Function using (_∘_; _⟨_⟩_)
  fromℕ : ℕ → List Bit
  fromℕ = proj₁ ∘ toDigits 2

  ℕ-setoid = PropEq.setoid ℕ

  open import Function using (id)
  open import Function.Bijection using (Bijection; Bijective)
  open import Function.Equality using (_⟶_)

  zeroIsZero : ∀ n → fromDigits (0× n) ≡ 0
  zeroIsZero zero = PropEq.refl
  zeroIsZero (suc n) rewrite zeroIsZero n = PropEq.refl

  toℕ-cong : ∀ {x y} → x ≈ y → toℕ x ≡ toℕ y
  toℕ-cong (equiv [] a b) rewrite zeroIsZero a | zeroIsZero b = PropEq.refl
  toℕ-cong (equiv (h ∷ t) a b) rewrite toℕ-cong (equiv t a b) = PropEq.refl

  fromℕ⟶ : ℕ-setoid ⟶ setoid
  fromℕ⟶ = record
    { _⟨$⟩_ = fromℕ
    ; cong = λ eq → ≡→≈ (PropEq.cong fromℕ eq)
    }

  toℕ⟶ : setoid ⟶ ℕ-setoid
  toℕ⟶ = record
    { _⟨$⟩_ = toℕ
    ; cong = toℕ-cong
    }


  fromℕ-inj : ∀ {x y} → fromℕ x ≈ fromℕ y → x ≡ y
  fromℕ-inj {x} {y} eq with toDigits 2 x | toDigits 2 y
  fromℕ-inj .{_} .{_} eq | xDig , PropEq.refl | yDig , PropEq.refl = toℕ-cong eq

  open import Data.Nat.DivMod

  bitToℕ : Bit → ℕ
  bitToℕ = Data.Fin.toℕ
 
  open Data.Nat using (_*_)
  +-inj₁ : ∀ c {a b} → c + a ≡ c + b → a ≡ b
  +-inj₁ zero eq = eq
  +-inj₁ (suc c) {a} {b} eq = +-inj₁ c {a} {b} (suc-inj eq)


  module DigitInj where
    open import Data.Nat.Properties using (isCommutativeSemiring)
    open import Algebra.Structures
    open IsCommutativeSemiring isCommutativeSemiring hiding (zero)
    open import Data.Empty using (⊥; ⊥-elim)

    finToℕ-inj : ∀ {base} {x y : Fin base} → finToℕ x ≡ finToℕ y → x ≡ y
    finToℕ-inj {.(suc _)} {zero} {zero} eq = PropEq.refl
    finToℕ-inj {.(suc _)} {zero} {suc y} ()
    finToℕ-inj {.(suc _)} {suc x} {zero} ()
    finToℕ-inj {.(suc _)} {suc x} {suc y} eq = PropEq.cong suc (finToℕ-inj (suc-inj eq))

    fin-not-enough : ∀ {base} → (x : Fin base) → ∀ whatever → finToℕ x ≡ base + whatever → ⊥
    fin-not-enough {.(suc _)} zero _ ()
    fin-not-enough {.(suc _)} (suc x) _ eq = fin-not-enough _ _ (Data.Nat.Properties.suc-injective eq)

    digit-inj2 : ∀ {base : ℕ} (h₁ h₂ : Fin base) (t₁ t₂ : ℕ)
                →   t₁ * base + finToℕ h₁
                  ≡ t₂ * base + finToℕ h₂
                → h₁ ≡ h₂ × t₁ ≡ t₂
    digit-inj2 x y zero zero eq = finToℕ-inj eq , PropEq.refl
    digit-inj2 {base} x y zero (suc ys) eq =
      ⊥-elim (fin-not-enough x (ys * base + finToℕ y) (PropEq.trans eq (+-assoc _ (ys * base) (finToℕ y))))
    digit-inj2 {base} x y (suc xs) zero eq =
      ⊥-elim (fin-not-enough y (xs * base + finToℕ x) (PropEq.trans (PropEq.sym eq) (+-assoc _ (xs * base) (finToℕ x))))
    digit-inj2 {base} x y (suc xs) (suc ys) eq =
       case digit-inj2 x y xs ys (+-inj₁ base  eq') of
       λ { (eq1 , eq2) → eq1 , PropEq.cong suc eq2 } where
      eq' =
        PropEq.trans
          (PropEq.sym (+-assoc base (xs * base) _))
          (PropEq.trans eq
            (+-assoc base (ys * base) _))

    digit-inj : ∀ {base : ℕ} (h₁ h₂ : Fin base) (t₁ t₂ : ℕ)
                →   finToℕ h₁ + t₁ * base
                  ≡ finToℕ h₂ + t₂ * base
                → h₁ ≡ h₂ × t₁ ≡ t₂
    digit-inj x y xs ys eq =
      digit-inj2 _ _ _ _ (PropEq.trans (+-comm (xs * _) (finToℕ x)) (PropEq.trans eq (+-comm _ (ys * _))))

  digit-inj = DigitInj.digit-inj

  toℕ-inj-zero : ∀ xs → toℕ xs ≡ 0 → All-zero xs
  toℕ-inj-zero [] eq = []
  toℕ-inj-zero (x ∷ xs) eq =
    case digit-inj x zero (toℕ xs) 0 eq of
      λ { (PropEq.refl , snd) → cons (toℕ-inj-zero xs snd) } 

  toℕ-inj2 : ∀ {x y} → toℕ x ≡ toℕ y → x ≈ᵢ y
  toℕ-inj2 {[]} {ys} eq = both-zero [] (toℕ-inj-zero ys (PropEq.sym eq))
  toℕ-inj2 {xs} {[]} eq = both-zero (toℕ-inj-zero xs eq) []
  toℕ-inj2 {x ∷ xs} {y ∷ ys} eq =
    case digit-inj x y (fromDigits xs) (fromDigits ys) eq of
      λ { (PropEq.refl , eq) → heads-match x xs ys (toℕ-inj2 eq) }

  bijective : Bijective toℕ⟶
  bijective = record
    { injective = λ e → ᵢ-to-≈ (toℕ-inj2 e)
    ; surjective = record 
       { from = fromℕ⟶
       ; right-inverse-of = proj₂ ∘ toDigits 2
       }
    }

  bijection-to-ℕ : Bijection setoid ℕ-setoid
  bijection-to-ℕ = record { bijective = bijective }
