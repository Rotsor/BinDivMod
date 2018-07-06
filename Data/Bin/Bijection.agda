module Data.Bin.Bijection where

  open import Relation.Binary.PropositionalEquality as PropEq hiding (inspect)
  open import Function.Bijection renaming (_∘_ to _∙_)
  import Function.Surjection
  open Function.Surjection using (module Surjection; module Surjective)
  open import Function.Equality using (_⟶_)
  open import Data.Nat using (ℕ; _*_; _+_)
  open import Data.Bin using (toℕ; Bin; fromBits; 2+_)
  open import Data.Product
  open import Data.Digit using (toDigits; fromDigits)

  ℕ-setoid = PropEq.setoid ℕ
  Bin-setoid = PropEq.setoid Bin

  fromℕ : ℕ → Bin
  fromℕ x = fromBits (proj₁ (toDigits 2 x))

-- hard to prove now
--  fromℕeq' : {n : ℕ} → fromℕ n ≡ fromℕ' n
--  fromℕeq' {x} with toDigits 2 x
--  fromℕeq' .{fromDigits d} | d , refl = {!!}

  fromℕ⟶ : ℕ-setoid ⟶ Bin-setoid
  fromℕ⟶ = record
    { _⟨$⟩_ = fromℕ
    ; cong = PropEq.cong fromℕ
    }

  toℕ⟶ : Bin-setoid ⟶ ℕ-setoid
  toℕ⟶ = record
    { _⟨$⟩_ = toℕ
    ; cong = PropEq.cong toℕ
    }

  open import Data.Digit using(Bit)
  open import Data.Bin using (fromBits; toBits; _1#; 0#; 0b; 1b)
  open import Data.List using (_∷_; []; _++_)
  open import Data.Fin using (suc; zero) renaming (toℕ to bitToℕ)

  fromBits-preserves-ℕ : ∀ x → toℕ (fromBits x) ≡ fromDigits x
  fromBits-preserves-ℕ [] = refl
  fromBits-preserves-ℕ (h ∷ t) with fromBits t | fromBits-preserves-ℕ t
  ... | 0# | zo with h
  ... | zero = PropEq.cong (λ x → x * 2) zo
  ... | suc zero = PropEq.cong (λ x → 1 + x * 2) zo
  ... | suc (suc ())
  fromBits-preserves-ℕ (h ∷ t) | l 1# | zoq = PropEq.cong (λ x → bitToℕ h + x * 2) zoq

  fromℕ-inj : ∀ {x y} → fromℕ x ≡ fromℕ y → x ≡ y
  fromℕ-inj {x} {y} eq with toDigits 2 x | toDigits 2 y
  fromℕ-inj {._} {._} eq | xDig , refl | yDig , refl = 
      PropEq.trans
          (PropEq.sym (fromBits-preserves-ℕ xDig))
       (PropEq.trans
          (PropEq.cong toℕ eq)
          (fromBits-preserves-ℕ yDig)
       )

  open import Data.Bin.BitListBijection 
    using (≈-refl; ≈-sym; ≈-trans; ≈ᵢ-trans; ≈ᵢ-sym; _≈ᵢ_; ᵢ-to-≈; ≈-to-ᵢ; All-zero; module All-zero; All-zero-respects-equivalence)
    renaming (setoid to bits-setoid; bijection-to-ℕ to BL-bijection-ℕ)

  open _≈ᵢ_
  open All-zero
  open import Relation.Binary using (module Setoid)
  module Bits = Setoid bits-setoid

  open Bits using (_≈_)

  open import Data.Product using (_,_; proj₂; proj₁)
  open import Function using (_∘_)

  open Data.List using(List)

  fromBits-zero : ∀ {l} → All-zero l → fromBits l ≡ 0#
  fromBits-zero [] = PropEq.refl
  fromBits-zero (All-zero.cons {t} z) with fromBits t | fromBits-zero z
  fromBits-zero (All-zero.cons z) | .0# | refl = PropEq.refl

  fromBitsCong : ∀ {i j} → i ≈ᵢ j → fromBits i ≡ fromBits j
  fromBitsCong (both-zero a-zero b-zero) =
     PropEq.trans (fromBits-zero a-zero)
      (PropEq.sym (fromBits-zero b-zero))
  fromBitsCong (heads-match h at bt eq) with fromBits at | fromBits bt | fromBitsCong eq
  fromBitsCong (heads-match Data.Bin.0b at bt eq) | 0# | .0# | refl = PropEq.refl
  fromBitsCong (heads-match Data.Bin.1b at bt eq) | 0# | .0# | refl = PropEq.refl
  fromBitsCong (heads-match (Data.Bin.2+ ()) at bt eq) | 0# | .0# | refl
  fromBitsCong (heads-match h at bt eq) | bs 1# | .(bs 1#) | refl = PropEq.refl

  fromBits⟶ : bits-setoid ⟶ Bin-setoid
  fromBits⟶ = record
    { _⟨$⟩_ = fromBits
    ; cong = λ e → fromBitsCong (≈-to-ᵢ e)
    }

  toBits⟶ : Bin-setoid ⟶ bits-setoid
  toBits⟶ = record
    { _⟨$⟩_ = toBits
    ; cong = λ { {i} .{_} PropEq.refl → Bits.refl }
    }
  
  open import Data.Product using (_×_)

  #1-inj : ∀ {a b} → a 1# ≡ b 1# → a ≡ b
  #1-inj refl = refl

  fromToBits-inverse : ∀ a → fromBits (toBits a) ≡ a
  fromToBits-inverse 0# = refl
  fromToBits-inverse ([] 1#) = refl
  fromToBits-inverse ((h ∷ t) 1#) with fromBits (toBits (t 1#)) | fromToBits-inverse (t 1#)
  ... | 0# | ()
  ... | l 1# | koko = PropEq.cong (λ x → (h ∷ x) 1#) (#1-inj koko)

  qqq : ∀ {xs} → (0b ∷ []) ≈ᵢ xs → [] ≈ᵢ xs
  qqq (both-zero a-zero b-zero) = both-zero [] b-zero
  qqq (heads-match .0b .[] bt x) = both-zero [] (cons (All-zero-respects-equivalence x []))

  toFromBits-inverse : ∀ a → (toBits (fromBits a)) ≈ᵢ a
  toFromBits-inverse [] = both-zero (cons []) []
  toFromBits-inverse (x ∷ xs) with fromBits xs | toFromBits-inverse xs
  toFromBits-inverse (0b ∷ xs) | 0# | w =
    heads-match 0b [] xs (qqq w) 
  toFromBits-inverse (1b ∷ xs) | 0# | w =
    heads-match 1b [] xs (qqq w)
  toFromBits-inverse ((2+ ()) ∷ xs) | 0# | w
  toFromBits-inverse (x ∷ xs) | bs 1# | w =
    heads-match x (bs ++ suc 0b ∷ []) xs w

  fromBits-inj : ∀ {x y} → fromBits x ≡ fromBits y → x ≈ y
  fromBits-inj eq =
    ≈-trans (≈-sym (ᵢ-to-≈ (toFromBits-inverse _)))
    (≈-trans (Setoid.reflexive bits-setoid (cong toBits eq)) (ᵢ-to-≈ (toFromBits-inverse _)))

  bijectiveFB : Bijective fromBits⟶
  bijectiveFB = record
    { injective = fromBits-inj
    ; surjective = record 
       { from = toBits⟶
       ; right-inverse-of = fromToBits-inverse
       }
    }

  BL-bijection-Bin : Bijection bits-setoid Bin-setoid
  BL-bijection-Bin = record
    { bijective = bijectiveFB
    }

  import Level
  ₀ = Level.zero
  open import Relation.Binary using ( Setoid)
  symBij : ∀ {A B : Setoid ₀ ₀} → Bijection A B → Bijection B A
  symBij {A} {B} bij = record {
      bijective = record 
        { injective = Surjection.injective surjection 
        ; surjective = record
           { right-inverse-of = left-inverse-of
           ; from = to }
        }
      ; to = from
    } where open Bijection bij

  megaBijection : Bijection ℕ-setoid Bin-setoid
  megaBijection = BL-bijection-Bin ∙ symBij BL-bijection-ℕ

  toℕ-inj : ∀ {x y} → toℕ x ≡ toℕ y → x ≡ y
  toℕ-inj {x} {y} eq = Surjection.injective (Bijection.surjection BL-bijection-Bin) (Bijective.injective (Bijection.bijective BL-bijection-ℕ) eq)

  fromToℕ-inverse : ∀ x → fromℕ (toℕ x) ≡ x
  fromToℕ-inverse x = kojo where
    kojo : fromℕ (toℕ x) ≡ x
    kojo = Bijective.right-inverse-of (Bijection.bijective megaBijection) x

  toFromℕ-inverse : ∀ x → toℕ (fromℕ x) ≡ x
  toFromℕ-inverse x = fromℕ-inj (fromToℕ-inverse _)

  bijective : Bijective fromℕ⟶
  bijective = record
    { injective = fromℕ-inj
    ; surjective = record 
       { from = toℕ⟶
       ; right-inverse-of = fromToℕ-inverse
       }
    }

  bijection : Bijection ℕ-setoid Bin-setoid
  bijection = record
    { bijective = bijective }
