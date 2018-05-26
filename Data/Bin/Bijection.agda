module Data.Bin.Bijection where

  open import Relation.Binary.PropositionalEquality as PropEq hiding (inspect)
  open import Function.Bijection renaming (_∘_ to _∙_)
  import Function.Surjection
  open Function.Surjection using (module Surjection; module Surjective)
  open import Function.Equality using (_⟶_)
  open import Data.Nat using (ℕ; _*_; _+_)
  open import Data.Bin using (toℕ; Bin; fromBits)
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

  open import Data.Digit
  open import Data.Bin using (fromBits; toBits; _1#; 0#)
  open import Data.List using (_∷_; [])
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
    using (∷-inj; []-∷-inj; ≈-sym; []-∷-cong; ∷-cong)
    renaming (setoid to bits-setoid; bijection-to-ℕ to BL-bijection-ℕ)

  open import Relation.Binary using (module Setoid)
  module Bits = Setoid bits-setoid

  open Bits using (_≈_)

  open import Data.Product using (_,_; proj₂; proj₁)

  fbc1 : ∀ {h t} → (t ≈ [] → fromBits t ≡ fromBits []) → h ∷ t ≈ [] → fromBits (h ∷ t) ≡ fromBits []
  fbc1 rec eq rewrite proj₁ ([]-∷-inj eq) | rec (proj₂ ([]-∷-inj eq)) = refl

  fbc2 : ∀ {x y xs ys} → (xs ≈ ys → fromBits xs ≡ fromBits ys) 
         → x ∷ xs ≈ y ∷ ys → fromBits (x ∷ xs) ≡ fromBits (y ∷ ys)
  fbc2 {x} {y} {xs} {ys} rec eq with ∷-inj eq
  ... | x≡y , xs≈ys with  fromBits xs | fromBits ys | rec xs≈ys
  fbc2 {zero} .{zero} {xs} {ys} _ _ | PropEq.refl , _ | 0# | .0# | PropEq.refl = refl
  fbc2 {suc zero} .{suc zero} {xs} {ys} _ _ | PropEq.refl , _ | 0# | .0# | PropEq.refl = refl
  fbc2 {suc (suc ())} .{_} {_} {_} _ _ | PropEq.refl , _ | 0# | .0# | PropEq.refl
  fbc2 {x} .{x} {xs} {ys} _ _ | PropEq.refl , _ | l 1# | .(l 1#) | PropEq.refl = refl

  open import Function using (_∘_)

  fromBitsCong-[] : ∀ {i} → i ≈ [] → fromBits i ≡ fromBits []
  fromBitsCong-[] {[]} = λ _ → refl
  fromBitsCong-[] {x ∷ xs} = fbc1 (fromBitsCong-[] {xs})

  fromBitsCong : ∀ {i j} → i ≈ j → fromBits i ≡ fromBits j
  fromBitsCong {x} {[]} = fromBitsCong-[] {x}
  fromBitsCong {[]} {y ∷ ys} = sym ∘ fbc1 (fromBitsCong-[] {ys}) ∘ ≈-sym
  fromBitsCong {x ∷ xs} {y ∷ ys} = fbc2 {x} {y} {xs} {ys} (fromBitsCong {xs} {ys})

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

  fbi-∷-0#-inj : ∀ {x xs} → fromBits (x ∷ xs) ≡ 0# → x ≡ zero × fromBits xs ≡ 0#
  fbi-∷-0#-inj {x} {xs} eq with fromBits xs
  fbi-∷-0#-inj {suc (suc ())} {_} _ | _
  fbi-∷-0#-inj {zero} {xs} eq | 0# = refl , refl
  fbi-∷-0#-inj {suc zero} {xs} () | 0#
  fbi-∷-0#-inj {x} {xs} () | l 1#

  fbi-∷-[]1#-inj : ∀ {x xs} → fromBits (x ∷ xs) ≡ [] 1# → x ≡ suc zero × fromBits xs ≡ 0#
  fbi-∷-[]1#-inj {x} {xs} eq with fromBits xs
  fbi-∷-[]1#-inj {suc (suc ())} {xs} _ | _
  fbi-∷-[]1#-inj {zero} {xs} () | 0#
  fbi-∷-[]1#-inj {suc zero} {xs} _ | 0# = refl , refl
  fbi-∷-[]1#-inj {x} {xs} () | _ 1#

  fbi-∷-∷1#-inj : ∀ {x xs h t} → fromBits (x ∷ xs) ≡ (h ∷ t) 1# → x ≡ h × fromBits xs ≡ t 1#
  fbi-∷-∷1#-inj {x} {xs} eq with fromBits xs
  fbi-∷-∷1#-inj {suc (suc ())} {xs} _ | _
  fbi-∷-∷1#-inj {zero} {xs} () | 0#
  fbi-∷-∷1#-inj {suc zero} {xs} () | 0#
  fbi-∷-∷1#-inj {x} {xs} .{x} .{l} refl | l 1# = refl , refl

  fbi1 : ∀ {x xs} → (fromBits xs ≡ 0# → xs ≈ [])
         → fromBits (x ∷ xs) ≡ 0# → x ∷ xs ≈ []
  fbi1 {x} {xs} rec eq with fbi-∷-0#-inj {x} {xs}  eq
  ... | x≡0 , xs≡0# = ≈-sym ([]-∷-cong (sym x≡0) (≈-sym (rec xs≡0#)))

  fbi-∷-inj : ∀ {x xs y ys} → fromBits (x ∷ xs) ≡ fromBits (y ∷ ys) → x ≡ y × fromBits xs ≡ fromBits ys
  fbi-∷-inj {x} {xs} {y} {ys} with fromBits xs | PropEq.inspect fromBits xs | fromBits ys | PropEq.inspect fromBits ys
  fbi-∷-inj {zero} {xs} {y} {ys}       | 0#     | record { eq = fbxs≡ } | _       | record { eq = refl } rewrite fbxs≡ =
    λ eq →  map sym sym (fbi-∷-0#-inj {y} {ys} (sym eq))
    where open Data.Product
  fbi-∷-inj {x} {xs} {zero} {ys}       | _      | record { eq = fbxs≡ } | 0#     | record { eq = fbys≡ } rewrite sym fbxs≡ | fbys≡ = fbi-∷-0#-inj {x} {xs}
  fbi-∷-inj {suc zero} {xs} {y} {ys}   | 0#     | record { eq = fbxs≡ } | _       | record { eq = refl } rewrite fbxs≡ = map sym sym ∘ fbi-∷-[]1#-inj {y} {ys} ∘ sym where open Data.Product
  fbi-∷-inj {x} {xs} {suc zero} {ys}   | _      | record { eq = fbxs≡ } | 0#      | record { eq = fbys≡ } rewrite fbys≡ | sym fbxs≡ = fbi-∷-[]1#-inj {x} {xs}
  fbi-∷-inj {x} {xs} {y} {ys}          | (lx 1#)| record { eq = fbxs≡ } | (ly 1#) | record { eq =  fbys≡ } rewrite fbxs≡ | fbys≡ = helper where
    helper : ∀ {x lx y ly} → (x ∷ lx) 1# ≡ (y ∷ ly) 1# → x ≡ y × lx 1# ≡ ly 1#
    helper refl = refl , refl
  fbi-∷-inj {suc (suc ())} | _ | _ | _ | _
  fbi-∷-inj {_} {_} {suc (suc ())} | _ | _ | _ | _

  fbi2 : ∀ {x xs y ys} → (fromBits xs ≡ fromBits ys → xs ≈ ys)
         → fromBits (x ∷ xs) ≡ fromBits (y ∷ ys) → x ∷ xs ≈ y ∷ ys
  fbi2 {x} {xs} {y} {ys} rec eq with fbi-∷-inj {x} {xs} {y} {ys} eq
  ... | x≡y , fbxs≡fbys with rec fbxs≡fbys
  ... | xs≈ys = ∷-cong x≡y xs≈ys

  fromBits-inj-[] : ∀ {x} → fromBits x ≡ fromBits [] → x ≈ []
  fromBits-inj-[] {x ∷ xs} = fbi1 (fromBits-inj-[] {xs})
  fromBits-inj-[] {[]} = λ _ → Data.Bin.BitListBijection.equiv Data.Nat.zero Data.Nat.zero []

  fromBits-inj : ∀ {x y} → fromBits x ≡ fromBits y → x ≈ y
  fromBits-inj {x ∷ xs} {y ∷ ys} = fbi2 (fromBits-inj {xs} {ys})
  fromBits-inj {[]} {y ∷ ys} = ≈-sym ∘ fbi1 (fromBits-inj-[] {ys}) ∘ sym
  fromBits-inj {xs} {[]} = fromBits-inj-[]

  #1-inj : ∀ {a b} → a 1# ≡ b 1# → a ≡ b
  #1-inj refl = refl

  fromToBits-inverse : ∀ a → fromBits (toBits a) ≡ a
  fromToBits-inverse 0# = refl
  fromToBits-inverse ([] 1#) = refl
  fromToBits-inverse ((h ∷ t) 1#) with fromBits (toBits (t 1#)) | fromToBits-inverse (t 1#)
  ... | 0# | ()
  ... | l 1# | koko = PropEq.cong (λ x → (h ∷ x) 1#) (#1-inj koko)

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
