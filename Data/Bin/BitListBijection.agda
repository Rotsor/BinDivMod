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

  module DigitInj where
    open import Relation.Binary using (StrictTotalOrder; module StrictTotalOrder)
    import Data.Nat.Properties
    open Data.Nat.Properties.≤-Reasoning
    open Data.Nat using (_<_; _≤_; s≤s)
    open import Data.Nat.Properties using (isCommutativeSemiring)
    open import Algebra.Structures

    open IsCommutativeSemiring isCommutativeSemiring hiding (zero)

    open import Relation.Nullary

    1+b+c>b : ∀ b c → ¬ 1 + b + c ≤ b
    1+b+c>b zero zero ()
    1+b+c>b (suc b) c (s≤s ≤) = 1+b+c>b b c ≤
    1+b+c>b zero c ()

    +-inj₁ : ∀ c {a b} → c + a ≡ c + b → a ≡ b
    +-inj₁ zero eq = eq
    +-inj₁ (suc c) {a} {b} eq = +-inj₁ c {a} {b} (suc-inj eq)

    open import Data.Empty

    digit-inj₁ : ∀ {base : ℕ} 
              (h : ℕ) → (h < base) 
              → (t₁ t₂ : ℕ)
              → t₁ * base ≡ h + t₂ * base
              → 0 ≡ h
    digit-inj₁ zero _ _ _ _ = PropEq.refl
    digit-inj₁ {suc b'} h h<b zero zero eq = PropEq.trans eq (sym (+-comm 0 h))
    digit-inj₁ {b} h h<b (suc n) zero eq rewrite (PropEq.trans (+-comm 0 h) (PropEq.sym eq)) =  ⊥-elim (1+b+c>b b (n * b) h<b)
    digit-inj₁ {zero} _ () _ _ eq
    digit-inj₁ {suc b'} (suc h) h<b zero (suc n) ()
    digit-inj₁ {b} h h<b (suc m) (suc n) eq = digit-inj₁ h h<b m n eq' where
      module P = PropEq
      eq' : m * b ≡ h + n * b
      eq' =  +-inj₁ b ( P.trans eq (P.trans (P.sym (+-assoc h b (n * b)))
                            (P.trans (P.cong (λ y → y + n * b) (+-comm h b)) (+-assoc b h (n * b)))))

    <-to-≤ : ∀ {a b} → a < b → a ≤ b
    <-to-≤ {zero} a<b = Data.Nat.z≤n
    <-to-≤ {suc n} (s≤s leq) = s≤s (<-to-≤ {n} leq)

    digit-inj₁' : ∀ {base : ℕ} 
              (h₁ h₂ : ℕ) → (h₁ < base) → (h₂ < base)
              → (t₁ t₂ : ℕ)
              → h₁ + t₁ * base ≡ h₂ + t₂ * base
              → h₁ ≡ h₂
    digit-inj₁' h zero h<b _ t1 t2 eq = PropEq.sym (digit-inj₁ h h<b t2 t1 (PropEq.sym eq))
    digit-inj₁' zero h _ h<b t1 t2 eq = digit-inj₁ h h<b t1 t2 eq
    digit-inj₁' {suc b} (suc h₁) (suc h₂) h₁<b h₂<b t1 t2 eq = PropEq.cong suc (digit-inj₁' {suc b} h₁ h₂ ( <-to-≤ h₁<b) (<-to-≤  h₂<b) t1 t2 (suc-inj eq))
    digit-inj₁' {zero} _ _ () () _ _ _

    finToℕ-inj : ∀ {base : ℕ} → {h₁ h₂ : Fin base} → finToℕ h₁ ≡ finToℕ h₂ → h₁ ≡ h₂
    finToℕ-inj {zero} {()} eq
    finToℕ-inj {suc b} {zero} {zero} eq = PropEq.refl
    finToℕ-inj {suc b} {suc h₁} {zero} ()
    finToℕ-inj {suc b} {zero} {suc h₂} ()
    finToℕ-inj {suc b} {suc h₁} {suc h₂} eq = PropEq.cong suc (finToℕ-inj {b} {h₁} {h₂} (suc-inj eq))

    fin<base : ∀ {base : ℕ} → (n : Fin base) → finToℕ n < base
    fin<base zero = s≤s Data.Nat.z≤n
    fin<base (suc n) = s≤s (fin<base n)

    *-inj₂ : ∀ {a b} c → ¬ c ≡ 0 → a * c ≡ b * c → a ≡ b
    *-inj₂ zero nonzero _ = ⊥-elim (nonzero PropEq.refl)
    *-inj₂ {zero} {zero} _ _ _ = PropEq.refl
    *-inj₂ {suc a} {zero} (suc c) _ ()
    *-inj₂ {zero} {suc b} (suc c) _ ()
    *-inj₂ {suc a} {suc b} (suc c) _ eq with *-inj₂ {a} {b} (suc c) (λ ()) (+-inj₁ (suc c) eq)
    ... | rec =  PropEq.cong suc rec

    digit-inj₁'' : ∀ {base : ℕ}
                (h₁ h₂ : Fin base)
                → (t₁ t₂ : ℕ)
                → finToℕ h₁ + t₁ * base ≡ finToℕ h₂ + t₂ * base
                → h₁ ≡ h₂ × t₁ ≡ t₂
    digit-inj₁'' {b} h₁ h₂ t₁ t₂ eq with (digit-inj₁' (finToℕ h₁) (finToℕ h₂) (fin<base h₁) (fin<base h₂) t₁ t₂ eq)
    ... | h2n-eq = finToℕ-inj h2n-eq ,  t-eq eq where
      bnz : ∀ (b : ℕ) (h₁ : Fin b) → ¬ b ≡ 0
      bnz b h₁ with b | h₁
      ... | 0 | ()
      ... | suc n | _ = λ ()

      t-eq : finToℕ h₁ + t₁ * b ≡ finToℕ h₂ + t₂ * b → t₁ ≡ t₂
      t-eq eq with eq
      ... | eqq rewrite h2n-eq =  *-inj₂ b (bnz b h₁) (+-inj₁ (finToℕ h₂) eqq)

  digit-inj : ∀ {base : ℕ} (h₁ h₂ : Fin base) (t₁ t₂ : ℕ)
              →   finToℕ h₁ + t₁ * base
                ≡ finToℕ h₂ + t₂ * base
              → h₁ ≡ h₂ × t₁ ≡ t₂
  digit-inj = DigitInj.digit-inj₁''

  ∷-cong : ∀ {h₁ h₂ t₁ t₂} → h₁ ≡ h₂ → t₁ ≈ t₂ → h₁ ∷ t₁ ≈ h₂ ∷ t₂
  ∷-cong {h} PropEq.refl (equiv l a b) = equiv (h ∷ l) a b
  
  []-∷-cong : ∀ {h t} → zero ≡ h → [] ≈ t → [] ≈ h ∷ t
  []-∷-cong .{zero} {t} PropEq.refl eq with patternMatch (λ x → x ≈ t) eq
  []-∷-cong .{zero} .{replicate b zero} PropEq.refl _
       | ._ , (equiv [] 0 b , ≡) = equiv [] 0 (suc b)
  []-∷-cong .{zero} .{_} PropEq.refl _ | ._ , (equiv [] (suc a) b , ())
  []-∷-cong .{zero} .{_} PropEq.refl _ | ._ , (equiv (h ∷ t) a b , ())

  smaller-toℕ-inj : ∀ {h t} → (0 ≡ fromDigits t → [] ≈ t) 
                    → 0 ≡ finToℕ h + fromDigits t * 2
                    → [] ≈ h ∷ t
  smaller-toℕ-inj {h} {t} rec eq with digit-inj zero h 0 (fromDigits t) eq
  ... | 0≡h , []≡ft = []-∷-cong 0≡h (rec []≡ft)

  toℕ-inj-[] : ∀ {y} → toℕ [] ≡ toℕ y → [] ≈ y
  toℕ-inj-[] {h ∷ t} eq with toℕ-inj-[] {t}
  ... | rec = smaller-toℕ-inj rec eq
  toℕ-inj-[] {[]} eq = equiv [] 0 0

  toℕ-inj : ∀ {x y} → toℕ x ≡ toℕ y → x ≈ y
  toℕ-inj {[]} {y} eq = toℕ-inj-[] {y} eq
  toℕ-inj {h ∷ t} {[]} eq with toℕ-inj-[] {t}
  ... | rec = ≈-sym (smaller-toℕ-inj rec (PropEq.sym eq))
  toℕ-inj {h₁ ∷ t₁} {h₂ ∷ t₂} eq with toℕ-inj {t₁} {t₂}
  ... | rec with digit-inj h₁ h₂ (fromDigits t₁) (fromDigits t₂) eq 
  ... | h₁≡h₂ , t₁≡t₂ = ∷-cong h₁≡h₂ (rec t₁≡t₂)

  toFromℕ-inverse : ∀ x → toℕ (fromℕ x) ≡ x
  toFromℕ-inverse x with (toDigits 2 x)
  toFromℕ-inverse .(fromDigits dig) | dig , PropEq.refl = PropEq.refl

  bijective : Bijective toℕ⟶
  bijective = record
    { injective = toℕ-inj
    ; surjective = record 
       { from = fromℕ⟶
       ; right-inverse-of = toFromℕ-inverse
       }
    }

  bijection-to-ℕ : Bijection setoid ℕ-setoid
  bijection-to-ℕ = record { bijective = bijective }
