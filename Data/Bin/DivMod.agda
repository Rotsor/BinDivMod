module Data.Bin.DivMod where

 import Data.Fin
 import Data.Product
 import Data.Bin
 import Data.Nat
 import Relation.Binary.PropositionalEquality
 import Data.Digit hiding (0b; 1b)
 import Data.List
 import Algebra
 import Algebra.Structures
 import Data.Bin.NatHelpers
 

 open Data.Bin using (Bin; toℕ; toBits; fromBits; _1#; 0#; 2+_; 0b; 1b)
 module PropEq = Relation.Binary.PropositionalEquality


 open Data.List using (_∷_; []; List)
 open Data.Nat using (ℕ; zero; suc)
 import Data.Nat.Properties

 open import Data.Bin.Utils

 open import Data.Bin.Bijection using (fromℕ-bijection; fromℕ; toℕ-inj; toFromℕ-inverse)

 import Data.Bin.Addition

 module Properties where

  open import Data.Bin.Multiplication
  open Data.Bin using () renaming (_+_ to _B+_; _*_ to _B*_)
  open Algebra.Structures using (IsCommutativeMonoid; module IsCommutativeSemiring)
  open PropEq
  open Data.Nat using (_+_; _*_)
  open Data.Nat.Properties using (isCommutativeSemiring)
  open IsCommutativeSemiring isCommutativeSemiring

 module Everything where

  open Data.Bin using (_1#; 0#; Bin; _+_; _*2; _*2+1; toℕ; ⌊_/2⌋; _*_; less)
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

  import Data.Bin.Bijection

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
  open import Data.Bin.Props

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

  open import Data.Bin.Minus using (_-?_; positive; negative; equal; Greater; greater)

  lemma1 : ∀ (f d q : Bin) → (d + f) + q * d ≡ f + (fromℕ 1 + q) * d
  lemma1 f d q =
    let open ≡-Reasoning in
    begin
      (d + f) + q * d
        ≡⟨ +-cong₁ {c = q * d} (+-comm d f) ⟩
      (f + d) + q * d
        ≡⟨ +-assoc f d (q * d) ⟩
      f + (d + q * d)
        ≡⟨ +-cong₂ {c = f} (+-cong₁ {c = q * d} (*-identityˡ {d})) ⟩
      f + ((fromℕ 1 * d) + q * d)
        ≡⟨ +-cong₂ {c = f} (PropEq.sym (*-distrib {fromℕ 1} {q} {d}))  ⟩
      f + (fromℕ 1 + q) * d
    ∎

  lemma2 : ∀ d q → d + q * d ≡ d + 0# + q * d
  lemma2 d q =  cong₂ _+_ (sym (proj₂ +-identity d)) (refl {x = q * d})
  
  open import Algebra.FunctionProperties
    using (LeftCancellative; RightCancellative; Cancellative)

  +-cancelˡ-< : LeftCancellative Data.Nat._<_ Data.Nat._+_
  +-cancelˡ-< c {y} {z} le =
    Data.Nat.Properties.+-cancelˡ-≤ c
      (subst₂ Data.Nat._≤_
        (PropEq.sym (Data.Nat.Properties.+-suc c y))
        (PropEq.refl {x = (Data.Nat._+_ c z)}) le)

  +-<-left-cancellative : LeftCancellative _<_ _+_
  +-<-left-cancellative c {a} {b} (less le) = less (+-cancelˡ-< (toℕ c) brr) where
     brr : toℕ c Data.Nat.+ toℕ a Data.Nat.< toℕ c Data.Nat.+ toℕ b
     brr = (subst₂ Data.Nat._<_
         (Data.Bin.Addition.+-is-addition c a)
         (Data.Bin.Addition.+-is-addition c b) le)

  +-elim₂ : RightCancellative _<_ _+_
  +-elim₂ {z} x y (less lt) rewrite +-is-addition x z | +-is-addition y z = less (Data.Bin.NatHelpers.+-elim₂ {toℕ x} {toℕ y} {toℕ z} lt)

  fixup-divmod :
    ∀ a d q r
    → a ≡ r + q * d
    → r < d + d
    → DivMod' a d
  fixup-divmod a d q r eq not-too-big =
    case r -? d of λ {
      (positive (greater diff PropEq.refl)) →
        result
          (fromℕ 1 + q)
          (diff 1# , +-<-left-cancellative d not-too-big)
          (PropEq.trans eq (lemma1 (diff 1#) d q));
      (negative x) → result q (r , Data.Bin.Minus.greater-to-< _ _ x) eq ;
      (equal PropEq.refl) →
        result
          (fromℕ 1 + q)
          (0# , 
            (+-<-left-cancellative
              d
              (subst (λ z → z < d + d) (PropEq.sym (proj₂ +-identity _)) not-too-big )) )
          (PropEq.trans eq (PropEq.trans (lemma2 d q) (lemma1 0# d q)))
       }

  lemma3 : ∀ r q d bit → (r + q * d) *2 + bit ≡ (r *2 + bit) + q *2 * d
  lemma3 r q d bit =
    let open ≡-Reasoning in
    begin
      (r + q * d) *2 + bit
        ≡⟨ +-cong₁ {c = bit}
           (begin
             (r + q * d) *2
               ≡⟨ *2-distrib r (q * d) ⟩
             r *2 + (q * d) *2
               ≡⟨ +-comm (r *2) ((q * d) *2) ⟩
             (q * d) *2 + r *2
           ∎) ⟩
      ((q * d) *2 + r *2) + bit
        ≡⟨ +-assoc ((q * d) *2) (r *2) (bit) ⟩
      (q * d) *2 + (r *2 + bit)
        ≡⟨ +-comm ((q * d) *2) (r *2 + bit) ⟩
      (r *2 + bit) + (q * d) *2
        ≡⟨ +-cong₂ {c = r *2 + bit} (*-*2-assoc {q} {d})  ⟩
      (r *2 + bit) + q *2 * d
    ∎

  dm-step :
    ∀ a d q (r : BinFin d) → a ≡ toBin r + q * d →
    ∀ w (bit : BinFin (fromℕ 2))
    → w ≡ (a *2 + proj₁ bit)
    → DivMod' w d
  dm-step ._ d q (r' , r'<d) refl ._ (bit , bit<2) refl =
    fixup-divmod
      _ d (q *2) (r' *2 + bit)
      (lemma3 r' q d bit)
      (<-pres₂ x*2≡x+x (*2-gives-space {r'} {d} {bit} r'<d (bit<2)))

  dmRec : (d : Bin) → {≢0 : False (d ≟ fromℕ 0)} → (a : Bin) → ((a' : Bin) → (a' < a) → DivMod' a' d) → DivMod' a d
  dmRec d {≢0} a rec =
    case a <? d of λ {
      (yes a<d) → result (0#) (a , a<d) (sym (+-identityʳ _)) ;
      (no ¬a<d) →
        case rec ⌊ a /2⌋ (helper ≢0 ¬a<d) of
          λ { (result q r eq) →
            dm-step ⌊ a /2⌋ d q r eq a (a %2 , %2<2) divMod2-lem } }

  import Data.Bin.Rec

  _divMod_ : (a : Bin) → (d : Bin) → {≢0 : False (d ≟ fromℕ 0)} → DivMod' a d
  _divMod_ a d {≡0} = Data.Bin.Rec.rec (λ x → DivMod' x d) (dmRec d {≡0}) a
