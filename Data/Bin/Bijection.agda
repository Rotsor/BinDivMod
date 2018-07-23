module Data.Bin.Bijection where

  open import Relation.Binary.PropositionalEquality as PropEq hiding (inspect)
  open import Function.Inverse renaming (_∘_ to _∙_)
  import Function.Surjection
  open Function.Surjection using (module Surjection; module Surjective)
  open import Function.Equality using (_⟶_)
  open import Data.Nat using (ℕ; _*_; _+_)
  open import Data.Bin using (toℕ; Bin; fromBits; 2+_; 0b; 1b)
  open import Data.Product
  open import Data.Digit using (Bit; toDigits; fromDigits)

  ℕ-setoid = PropEq.setoid ℕ
  Bin-setoid = PropEq.setoid Bin

  import Data.Fin
  pattern 1+ x = Data.Nat.suc x

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

  open import Data.Bin.BitListBijection 
    using (_≈_; All-zero; module All-zero; All-zero-respects-equivalence)
    renaming (setoid to bits-setoid; bijection-to-ℕ to Bits-bijection-ℕ)

  open _≈_
  open All-zero
  open import Relation.Binary using (module Setoid)
  module Bits = Setoid bits-setoid

  open import Data.Product using (_,_; proj₂; proj₁)
  open import Function using (_∘_)

  open Data.List using(List)

  fromBits-zero : ∀ {l} → All-zero l → fromBits l ≡ 0#
  fromBits-zero [] = PropEq.refl
  fromBits-zero (All-zero.cons {t} z) with fromBits t | fromBits-zero z
  fromBits-zero (All-zero.cons z) | .0# | refl = PropEq.refl

  fromBitsCong : ∀ {i j} → i ≈ j → fromBits i ≡ fromBits j
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
    ; cong = fromBitsCong
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
  ... | l 1# | eq = PropEq.cong (λ x → (h ∷ x) 1#) (#1-inj eq)

  qqq : ∀ {xs} → (0b ∷ []) ≈ xs → [] ≈ xs
  qqq (both-zero a-zero b-zero) = both-zero [] b-zero
  qqq (heads-match .0b .[] bt x) = both-zero [] (cons (All-zero-respects-equivalence x []))

  toFromBits-inverse : ∀ a → (toBits (fromBits a)) ≈ a
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
    Bits.trans (Bits.sym (toFromBits-inverse _))
    (Bits.trans (Setoid.reflexive bits-setoid (cong toBits eq)) (toFromBits-inverse _))

  open import Function.Inverse using (Inverse; _InverseOf_)

  inverseFB : toBits⟶ InverseOf fromBits⟶
  inverseFB = record
    {
      left-inverse-of = toFromBits-inverse;
      right-inverse-of = fromToBits-inverse
    }

  Bits-inverse-Bin : Inverse bits-setoid Bin-setoid
  Bits-inverse-Bin = record
    { inverse-of = inverseFB
    }

  fromℕ-inverse : Inverse ℕ-setoid Bin-setoid
  fromℕ-inverse =
    Bits-inverse-Bin
    ∙ Function.Inverse.sym (Function.Inverse.fromBijection Bits-bijection-ℕ)

  bijection-is-reasonable1 :
    Function.Equality._⟨$⟩_ (Inverse.to fromℕ-inverse) ≡ fromℕ
  bijection-is-reasonable1 = PropEq.refl

  bijection-is-reasonable2 :
    Function.Equality._⟨$⟩_ (Inverse.from fromℕ-inverse) ≡ toℕ
  bijection-is-reasonable2 = PropEq.refl


  toℕ-inverse = Function.Inverse.sym fromℕ-inverse
  toℕ-bijection = Inverse.bijection toℕ-inverse
  fromℕ-bijection = Inverse.bijection fromℕ-inverse

  toℕ-inj = Inverse.injective toℕ-inverse
  fromℕ-inj = Inverse.injective fromℕ-inverse
  fromToℕ-inverse = Inverse.left-inverse-of toℕ-inverse
  toFromℕ-inverse = Inverse.right-inverse-of toℕ-inverse
