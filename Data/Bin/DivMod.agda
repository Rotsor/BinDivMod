module Data.Bin.DivMod where

 import Data.Fin
 import Data.Product
 import Data.Bin
 import Data.Nat
 import Relation.Binary.PropositionalEquality
 import Data.Digit
 import Data.List
 import Algebra
 import Algebra.Structures
 import Data.Bin.NatHelpers
 

 open Data.Bin using (Bin; toℕ; toBits; fromBits; _1#; 0#)
 module PropEq = Relation.Binary.PropositionalEquality


 open Data.List using (_∷_; []; List)
 open Data.Nat using (ℕ; zero; suc)
 import Data.Nat.Properties

 open import Data.Bin.Utils

 module Properties where

  open import Data.Bin.Bijection using (bijection; fromℕ)

  open import Data.Bin.Addition
  open import Data.Bin.Multiplication
  open Data.Bin using () renaming (_+_ to _B+_; _*_ to _B*_)
  open Algebra.Structures using (IsCommutativeMonoid; module IsCommutativeSemiring)
  open PropEq
  open Data.Nat using (_+_; _*_)
  open Data.Nat.Properties using (isCommutativeSemiring)
  open IsCommutativeSemiring isCommutativeSemiring

 module Everything where

  open Data.Bin using (_1#; 0#; Bin; _+_; _*2; _*2+1; fromℕ; toℕ; ⌊_/2⌋; _*_; less)
  open import Data.Bin.Properties using (<-strictTotalOrder)
  open import Function
  open Data.Product
  open import Relation.Binary
  open Relation.Binary.PropositionalEquality renaming (setoid to ≡-setoid)
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open Data.Fin using (zero; suc)
  open Data.List using (_∷_; [])

  open StrictTotalOrder <-strictTotalOrder hiding (trans)

  open import Data.Bin.Minus using (_-_)

  BinFin : Bin → Set
  BinFin n = ∃ λ x → x < n

  toBin : ∀ {x} → BinFin x → Bin
  toBin = proj₁

{-  data DivMod : Bin → Bin → Set where
    result : ∀ {divisor : Bin} (q : Bin) (r : BinFin divisor) → DivMod (toBin r + q * divisor) divisor-}

  data DivMod' (dividend : Bin) (divisor : Bin) : Set where
    result : (q : Bin) (r : BinFin divisor) → (eq : dividend ≡ toBin r + q * divisor) → DivMod' dividend divisor

  open Data.Digit

  open Data.Bin using (addBitLists; addBits; toBits; fromBits)
  
  open import Data.List using (List; _++_; [_]; [])
  open import Data.Empty

  open import Data.Bin.Bijection using (fromToBits-inverse)

  import Data.Bin.Multiplication

  open Algebra.Structures using (module IsCommutativeMonoid)

  import Data.Bin.Props
  open Data.Bin.Props using (*-distrib; *2-is-2*; *2-distrib)
  open IsCommutativeMonoid Data.Bin.Props.bin-+-is-comm-monoid using ()
    renaming (identity to +-identity; comm to +-comm; assoc to +-assoc)


  open IsCommutativeMonoid Data.Bin.Props.bin-*-is-comm-monoid using () renaming (comm to *-comm)


  *-distribˡ : ∀ {a b c} → c * (a + b) ≡ c * a + c * b
  *-distribˡ {a} {b} {c} = *-comm c (a + b) ⟨ trans ⟩ *-distrib {a} {b} {c} ⟨ trans ⟩ cong₂ _+_ (*-comm a c) (*-comm b c)


  *-*2-assoc : ∀ {a b} → (a * b) *2 ≡ a *2 * b
  *-*2-assoc {a} {b} = Data.Bin.Multiplication.*-*2-comm a b

  *2-cong : ∀ {a b} → a ≡ b → a *2 ≡ b *2
  *2-cong = cong _*2

  
  +-cong₁ : ∀ {a b c} → a ≡ b → a + c ≡ b + c
  +-cong₁ {c = c} = cong (λ z → z + c)

  +-cong₂ : ∀ {a b c} → a ≡ b → c + a ≡ c + b
  +-cong₂ {c = c} = cong (λ z → c + z)


  +-identityʳ = proj₂ +-identity

  divMod2-lem : ∀ {a} → a ≡ ⌊ a /2⌋ *2 + a %2
  divMod2-lem {0#} = refl
  divMod2-lem {[] 1#} = refl
  divMod2-lem {(zero ∷ xs) 1#} = sym (+-identityʳ (⌊ (zero ∷ xs) 1# /2⌋ *2))
  divMod2-lem {(suc zero ∷ xs) 1#} = Data.Bin.Multiplication.∷1#-interpretation (suc zero) xs
                               ⟨ trans ⟩ +-comm ([] 1#) ((zero ∷ xs) 1#)
  divMod2-lem {(suc (suc ()) ∷ xs) 1#}

  import Relation.Binary.EqReasoning


  z<nz : ∀ l → 0# < l 1#
  z<nz l with (toℕ (l 1#)) | inspect toℕ (l 1#)
  ... | zero | [ ≡ ] with Data.Bin.Bijection.toℕ-inj {l 1#} {0#} ≡
  ... | ()
  z<nz l | suc n | [ eq ] = Data.Bin.less (subst (λ x → Data.Nat._≤_ 1 x) (sym eq) (Data.Nat.s≤s Data.Nat.z≤n))

  1+≢0 : ∀ l → toℕ (l 1#) ≢ 0
  1+≢0 l eq with Data.Bin.Bijection.toℕ-inj {l 1#} {0#} eq
  ... | ()

  helper' : ∀ l → ⌊ l 1# /2⌋ < l 1#
  helper' [] = Data.Bin.less (Data.Nat.s≤s Data.Nat.z≤n)
  helper' (x ∷ xs) = Data.Bin.less (Data.Bin.NatHelpers.kojojo x (toℕ (xs 1#)) (1+≢0 xs))

  helper : ∀ {a} {d} → (≢0 : False (d ≟ fromℕ 0)) → ¬ (a < d) → ⌊ a /2⌋ < a
  helper {_} {0#} () _
  helper {0#} {l 1#} _ a≮d = ⊥-elim (a≮d (z<nz l))
  helper {l 1#} _ _ = helper' l

  open import Data.Sum

  _≤_ : Bin → Bin → Set
  a ≤ b = a ≡ b ⊎ a < b

  ¬>→< : ∀ {a b} → ¬ (b ≤ a) → a < b
  ¬>→< {a} {b} a≰b with compare a b
  ... | tri< a<b _ _ = a<b
  ... | tri≈ _ a≡b _ = ⊥-elim (a≰b (inj₁ (sym a≡b))) 
  ... | tri> _ _ a>b = ⊥-elim (a≰b (inj₂ a>b)) 

  import Data.Bin.Addition
  *2-gives-space : ∀ {x y z} → (x < y) → z < fromℕ 2 → x *2 + z < y *2
  *2-gives-space {x} {y} {z} (less x<y) (less z<2) = less (finalize (Data.Bin.NatHelpers.*2-gives-space x<y z<2)) where
    open Data.Nat using () renaming (_*_ to _ℕ*_; _+_ to _ℕ+_; _<_ to _ℕ<_)
 
    eq1 : toℕ x ℕ* 2 ℕ+ toℕ z ≡ toℕ (x *2 + z)
    eq1 = sym (Data.Bin.Addition.+-is-addition (x *2) z ⟨ trans ⟩ cong (λ q → q ℕ+ toℕ z) (Data.Bin.Multiplication.*2-is-*2 x))
    eq2 : toℕ y ℕ* 2 ≡ toℕ (y *2)
    eq2 = sym (Data.Bin.Multiplication.*2-is-*2 y)

    finalize : toℕ x ℕ* 2 ℕ+ toℕ z ℕ< toℕ y ℕ* 2 → toℕ (x *2 + z) ℕ< toℕ (y *2)
    finalize = subst₂  _ℕ<_ eq1 eq2

  <-pres₁ : ∀ {a b c} → a ≡ b → a < c → b < c
  <-pres₁ refl eq = eq

  <-pres₂ : ∀ {a b c} → a ≡ b → c < a → c < b
  <-pres₂ refl eq = eq

  *-identityˡ : ∀ {x} → [] 1# * x ≡ x
  *-identityˡ = refl

  x*2≡x+x : ∀ {x} → x *2 ≡ x + x
  x*2≡x+x {x} = *2-is-2* x ⟨ trans ⟩ *-distrib {[] 1#} {[] 1#} {x} ⟨ trans ⟩ cong₂ _+_ (*-identityˡ {x}) (*-identityˡ {x})

  %2<2 : ∀ {x} → x %2 < fromℕ 2
  %2<2 {0#} = Data.Bin.less (Data.Nat.s≤s Data.Nat.z≤n)
  %2<2 {[] 1#} = Data.Bin.less (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))
  %2<2 {(zero ∷ xs) 1#} = Data.Bin.less (Data.Nat.s≤s Data.Nat.z≤n)
  %2<2 {(suc zero ∷ xs) 1#} = Data.Bin.less (Data.Nat.s≤s (Data.Nat.s≤s Data.Nat.z≤n))
  %2<2 {(suc (suc ()) ∷ xs) 1#}

  -+-elim : ∀ {x z} → ¬ x < z → x - z + z ≡ x
  -+-elim = Data.Bin.Minus.-+-elim'

  open import Data.Bin.Addition using (+-is-addition)

  +-elim₂ : ∀ {x y z} → x + z < y + z → x < y
  +-elim₂ {x} {y} {z} (less lt) rewrite +-is-addition x z | +-is-addition y z = less (Data.Bin.NatHelpers.+-elim₂ {toℕ x} {toℕ y} {toℕ z} lt)

  magic : ∀ {r d} → ¬ r < d → r < d + d → r - d < d
  magic {r} {d} r≮d r<d+d = +-elim₂ {z = d} (<-pres₁ (sym (-+-elim r≮d)) r<d+d)

  data Irr (A : Set) : Set where
   irr : A → Irr A

  dmRec : (d : Bin) → {≢0 : False (d ≟ fromℕ 0)} → (a : Bin) → ((a' : Bin) → (a' < a) → DivMod' a' d) → DivMod' a d
  dmRec d {≢0} a rec with a <? d
  ... | yes a<d = result (0#) (a , a<d) (sym (+-identityʳ _))
  ... | no ¬a<d with rec ⌊ a /2⌋ (helper ≢0 ¬a<d)
  ... | (result q (r' , r'<d) a/2≡r'+q*d) with ((r' *2) + a %2) | inspect (λ a → ((r' *2) + a %2)) a
  ... | r | [ r-definition ] with r <? d | irr a≡r+q*2*d where
     open ≡-Reasoning
     a≡r+q*2*d : a ≡ r + q *2 * d
     a≡r+q*2*d = 
       begin
         a
           ≡⟨ divMod2-lem ⟩
         ⌊ a /2⌋ *2 + a %2
           ≡⟨ +-cong₁ {c = a %2}
              (begin
                ⌊ a /2⌋ *2
                  ≡⟨ *2-cong a/2≡r'+q*d ⟩
                (r' + q * d) *2
                  ≡⟨ *2-distrib r' (q * d) ⟩
                r' *2 + (q * d) *2
                  ≡⟨ +-comm (r' *2) ((q * d) *2) ⟩
                (q * d) *2 + r' *2
              ∎) ⟩
         ((q * d) *2 + r' *2) + a %2
           ≡⟨ +-assoc ((q * d) *2) (r' *2) (a %2) ⟩
         (q * d) *2 + (r' *2 + a %2)
           ≡⟨ +-comm ((q * d) *2) (r' *2 + a %2) ⟩
         (r' *2 + a %2) + (q * d) *2
           ≡⟨ +-cong₂ {c = r' *2 + a %2} (*-*2-assoc {q} {d})  ⟩
         (r' *2 + a %2) + q *2 * d
           ≡⟨ +-cong₁ {c = q *2 * d} r-definition ⟩
         r + q *2 * d
       ∎
  ... | yes r<d | (irr a≡r+q*2*d) = result (q *2) (r , r<d) a≡r+q*2*d
  ... | no ¬r<d | (irr a≡r+q*2*d) = result (fromℕ 1 + (q *2)) (r - d , r-d<d) correct
    where
      r<2d : r < d + d
      r<2d = <-pres₁ r-definition (<-pres₂ {c = (r' *2) + a %2} x*2≡x+x (*2-gives-space r'<d (%2<2 {a})))
      r-d<d : r - d < d
      r-d<d = magic ¬r<d r<2d
      oldProof : a ≡ r + q *2 * d
      oldProof = a≡r+q*2*d
      open ≡-Reasoning
      correct : a ≡ (r - d) + (fromℕ 1 + q *2) * d
      correct = sym $
        begin
          (r - d) + (fromℕ 1 + q *2) * d
            ≡⟨ +-cong₂ {(fromℕ 1 + q *2) * d} {d + q *2 * d} {r - d} 
                 (begin
                  (fromℕ 1 + q *2) * d
                   ≡⟨ *-distrib {fromℕ 1} {q *2} {d} ⟩
                  fromℕ 1 * d + q *2 * d
                   ≡⟨ refl ⟩
                  d + q *2 * d
                 ∎ ) ⟩
          (r - d) + (d + q *2 * d)
            ≡⟨ sym (+-assoc (r - d) d (q *2 * d)) ⟩
          (r - d + d) + q *2 * d
            ≡⟨ +-cong₁ {r - d + d} {r} {q *2 * d} (-+-elim ¬r<d)  ⟩
          r + q *2 * d
            ≡⟨ sym oldProof ⟩
          a
        ∎

  import Data.Bin.Rec

  _divMod_ : (a : Bin) → (d : Bin) → {≢0 : False (d ≟ fromℕ 0)} → DivMod' a d
  _divMod_ a d {≡0} = Data.Bin.Rec.rec (λ x → DivMod' x d) (dmRec d {≡0}) a
