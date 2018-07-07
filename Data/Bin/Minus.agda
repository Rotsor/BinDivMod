module Data.Bin.Minus where

  open import Data.Bin hiding (suc; fromℕ)
  open Data.Bin using (2+_)
  open import Data.Bin.Bijection using (fromℕ)
  open import Data.Fin hiding (_-_; _+_; toℕ; _<_; fromℕ)
  open import Data.List
  open import Data.Digit
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat using (ℕ; _∸_; suc; zero) renaming (_+_ to _ℕ+_)

  infixl 6 _-?_
  infixl 6 _-_

  open import Function

  pred' : Bin → Bin
  pred' 0# = 0#
  pred' ([] 1#) = 0#
  pred' ((zero ∷ t) 1#) = case Data.Bin.pred t of
    λ {
      0# → [] 1# ;
      (t' 1#) → (suc zero ∷ t') 1#
    }
  pred' ((suc zero ∷ t) 1#) = (zero ∷ t) 1#
  pred' ((suc (suc ()) ∷ _) 1#)

  open import Data.Sum
  open import Data.Unit

  data Greater (a b : Bin) : Set where
   greater : ∀ (diff : Bin⁺) → b + diff 1# ≡ a → Greater a b
  
  data Difference (a b : Bin) : Set where
    positive : Greater a b → Difference a b
    negative : Greater b a → Difference a b
    equal : a ≡ b → Difference a b

  open import Relation.Nullary

  open import Algebra.Structures

  import Data.Bin.Addition
  open IsCommutativeMonoid Data.Bin.Addition.is-commutativeMonoid
    using (identity; identityˡ)
    renaming (comm to +-comm; assoc to +-assoc)

  open import Data.Product
  identityʳ = proj₂ identity

  ∷-pred : Bit → Bin⁺ → Bin⁺
  ∷-pred zero [] = []
  ∷-pred zero (h ∷ t) = suc zero ∷ ∷-pred h t
  ∷-pred (suc zero) l = zero ∷ l
  ∷-pred (suc (suc ())) l

  open Relation.Binary.PropositionalEquality.≡-Reasoning

  open import Data.Bin.Multiplication using (∷1#-interpretation)

  open import Function using (_⟨_⟩_)

  seems-trivial : ∀ xs → (zero ∷ xs) 1# + [] 1# ≡ (suc zero ∷ xs) 1#
  seems-trivial xs = cong (λ q → q + [] 1#) (∷1#-interpretation zero xs ⟨ trans ⟩ (identityˡ (xs 1# *2))) ⟨ trans ⟩ +-comm (xs 1# *2) ([] 1#) ⟨ trans ⟩ sym (∷1#-interpretation (suc zero) xs)

  open import Data.Bin.Props

  carry : ∀ t → [] 1# + (suc zero ∷ t) 1# ≡ ([] 1# + t 1#) *2
  carry t =
   begin
    [] 1# + (suc zero ∷ t) 1#
     ≡⟨ cong (_+_ ([] 1#)) (∷1#-interpretation (suc zero) t) ⟩
    [] 1# + ([] 1# + t 1# *2)
     ≡⟨ sym (+-assoc ([] 1#) ([] 1#) (t 1# *2)) ⟩
    [] 1# *2 + (t 1# *2)
     ≡⟨ sym (*2-distrib ([] 1#) (t 1#)) ⟩
    ([] 1# + t 1#) *2
   ∎

  1+∷-pred : ∀ h t → [] 1# + (∷-pred h t) 1# ≡ (h ∷ t) 1#
  1+∷-pred zero [] = refl
  1+∷-pred zero (x ∷ xs) =
   begin
    [] 1# + (suc zero ∷ ∷-pred x xs) 1#
     ≡⟨ carry (∷-pred x xs) ⟩
    ([] 1# + (∷-pred x xs) 1#) *2
     ≡⟨ cong _*2 (1+∷-pred x xs) ⟩
    (x ∷ xs) 1# *2
     ≡⟨ refl ⟩
    (zero ∷ x ∷ xs) 1#
   ∎
  1+∷-pred (suc zero) t = +-comm ([] 1#) ((zero ∷ t) 1#) ⟨ trans ⟩ seems-trivial t
  1+∷-pred (suc (suc ())) t

  data Comparison (A : Set) : Set where
    greater : A → Comparison A
    equal : Comparison A
    less : A → Comparison A

  
  map-cmp : {A B : Set} → (A → B) → Comparison A → Comparison B
  map-cmp f (greater a) = greater (f a)
  map-cmp f (less a) = less (f a)
  map-cmp f equal = equal

  _%f_ : ∀ {b} → Fin (suc b) → Fin (suc b) → Comparison (Fin b)
  zero %f zero = equal
  zero %f suc b = less b
  suc a %f zero = greater a
  _%f_ {suc base} (suc a) (suc b) = map-cmp inject₁ (a %f b)
  _%f_ {zero} (suc ()) (suc ())


  _*2-1 : Bin⁺ → Bin⁺
  [] *2-1 = []
  (suc zero ∷ t) *2-1 = suc zero ∷ zero ∷ t
  (zero ∷ t) *2-1 = suc zero ∷ (t *2-1)
  (suc (suc ()) ∷ t) *2-1

  _*2+1' : Bin⁺ → Bin⁺
  l *2+1' = suc zero ∷ l


  addBit : Bin⁺ → Comparison (Fin 1) → Bin⁺
  addBit gt (greater zero) = gt *2+1'
  addBit gt equal = zero ∷ gt
  addBit gt (less zero) = gt *2-1
  addBit gt (less (suc ()))
  addBit gt (greater (suc ()))

  open import Data.Bin.Utils

  *2-1-lem : ∀ d → (d *2-1) 1# + [] 1# ≡ d 1# *2
  *2-1-lem [] = refl
  *2-1-lem (zero ∷ xs) = 
   begin
    (zero ∷ xs) *2-1 1# + [] 1#
     ≡⟨ refl ⟩
    (suc zero ∷ (xs *2-1)) 1# + [] 1#
     ≡⟨ +-comm ((suc zero ∷ xs *2-1) 1#) ([] 1#)  ⟩
    [] 1# + (suc zero ∷ (xs *2-1)) 1#
     ≡⟨ carry (xs *2-1) ⟩
    ([] 1# + (xs *2-1) 1#) *2
     ≡⟨ cong _*2 (+-comm ([] 1#) ((xs *2-1) 1#)) ⟩
    ((xs *2-1) 1# + [] 1#) *2
     ≡⟨ cong _*2 (*2-1-lem xs) ⟩
    (xs 1# *2) *2
     ≡⟨ refl ⟩
    (zero ∷ xs) 1# *2
   ∎
  *2-1-lem (suc zero ∷ xs) = 
   begin
    (suc zero ∷ zero ∷ xs) 1# + [] 1#
     ≡⟨ cong (λ q → q + [] 1#) (∷1#-interpretation (suc zero) (zero ∷ xs)) ⟩
    [] 1# + (zero ∷ xs) 1# *2 + [] 1#
     ≡⟨ refl ⟩
    [] 1# + xs 1# *2 *2 + [] 1#
     ≡⟨ +-comm ([] 1# + xs 1# *2 *2) ([] 1#) ⟩
    [] 1# + ([] 1# + xs 1# *2 *2)
     ≡⟨ sym (+-assoc ([] 1#) ([] 1#) (xs 1# *2 *2)) ⟩
    [] 1# *2 + xs 1# *2 *2
     ≡⟨ sym (*2-distrib ([] 1#) (xs 1# *2)) ⟩
    ([] 1# + xs 1# *2) *2
     ≡⟨ cong _*2 (sym (∷1#-interpretation (suc zero) xs)) ⟩
    (suc zero ∷ xs) 1# *2
     ≡⟨ refl ⟩
    (zero ∷ suc zero ∷ xs) 1#
   ∎
  *2-1-lem (suc (suc ()) ∷ xs)

  addBit-lem : ∀ x y d → addBit d (x %f y) 1# + bitToBin y ≡ d 1# *2 + bitToBin x
  addBit-lem zero zero d = refl
  addBit-lem (suc zero) zero d = refl
  addBit-lem zero (suc zero) d = *2-1-lem d ⟨ trans ⟩ sym (identityʳ (d 1# *2))
  addBit-lem (suc zero) (suc zero) d = refl
  addBit-lem (suc (suc ())) _ d
  addBit-lem _ (suc (suc ())) d

  +-cong₁ : ∀ {z} {x y} → x ≡ y → x + z ≡ y + z
  +-cong₁ {z} = cong (λ q → q + z)

  +-cong₂ : ∀ {z} {x y} → x ≡ y → z + x ≡ z + y
  +-cong₂ {z} = cong (λ q → z + q)

  refineGt : ∀ xs ys (x y : Bit) → Greater (xs 1#) (ys 1#) → Greater ((x ∷ xs) 1#) ((y ∷ ys) 1#)
  refineGt xs ys x y (greater d ys+d=xs) = greater (addBit d (x %f y)) good where
    good : (y ∷ ys) 1# + addBit d (x %f y) 1# ≡ (x ∷ xs) 1#
    good =
     begin
      (y ∷ ys) 1# + addBit d (x %f y) 1#
       ≡⟨ +-cong₁ {addBit d (x %f y) 1#} (∷1#-interpretation y ys) ⟩
      bitToBin y + (ys 1#) *2 + addBit d (x %f y) 1#
       ≡⟨ +-comm (bitToBin y + (ys 1#) *2) (addBit d (x %f y) 1#) ⟩
      addBit d (x %f y) 1# + (bitToBin y + (ys 1#) *2)
       ≡⟨ sym (+-assoc (addBit d (x %f y) 1#) (bitToBin y) ((ys 1#) *2)) ⟩
      (addBit d (x %f y) 1# + bitToBin y) + (ys 1#) *2
       ≡⟨ +-cong₁ {(ys 1#) *2} (addBit-lem x y d) ⟩
      (d 1# *2 + bitToBin x) + (ys 1#) *2
       ≡⟨ +-cong₁ {(ys 1#) *2} (+-comm (d 1# *2) (bitToBin x)) ⟩
      (bitToBin x + d 1# *2 ) + (ys 1#) *2
       ≡⟨  +-assoc (bitToBin x) (d 1# *2) ((ys 1#) *2) ⟩
      bitToBin x + (d 1# *2 + (ys 1#) *2)
       ≡⟨ +-cong₂ {bitToBin x} (+-comm (d 1# *2) ((ys 1#) *2)) ⟩
      bitToBin x + ((ys 1#) *2 + d 1# *2)
       ≡⟨ +-cong₂ {bitToBin x} (sym (*2-distrib (ys 1#) (d 1#))) ⟩
      bitToBin x + (ys 1# + d 1#) *2
       ≡⟨ +-cong₂ {bitToBin x} (cong _*2 ys+d=xs) ⟩
      bitToBin x + xs 1# *2
       ≡⟨ sym (∷1#-interpretation x xs) ⟩
      (x ∷ xs) 1#
     ∎

  compare-bit : ∀ a b xs → Difference ((a ∷ xs) 1#) ((b ∷ xs) 1#)
  compare-bit 0b 0b xs = equal refl
  compare-bit 1b 0b xs = positive (greater [] (seems-trivial xs))
  compare-bit 0b 1b xs = negative (greater [] (seems-trivial xs))
  compare-bit 1b 1b xs = equal refl
  compare-bit (2+ ()) _ xs
  compare-bit _ (2+ ()) xs

  _-⁺_ : ∀ a b → Difference (a 1#) (b 1#)
  [] -⁺ [] = equal refl
  [] -⁺ (x ∷ xs) = negative (greater (∷-pred x xs) (1+∷-pred x xs))
  (x ∷ xs) -⁺ [] = positive (greater (∷-pred x xs) (1+∷-pred x xs))
  (x ∷ xs) -⁺ (y ∷ ys) =
    case xs -⁺ ys of
      λ {
        (positive gt) → positive (refineGt xs ys x y gt) ;
        (negative lt) → negative (refineGt ys xs y x lt) ;
        (equal refl) → compare-bit _ _ xs 
     }

  _-?_ : ∀ a b → Difference a b
  0# -? 0# = equal refl
  a 1# -? 0# = positive (greater a (identityˡ (a 1#)))
  0# -? a 1# = negative (greater a (identityˡ (a 1#)))
  a 1# -? b 1# = a -⁺ b

  _%⁺_ : Bin⁺ → Bin⁺ → Comparison Bin⁺
  [] %⁺ [] = equal
  (h ∷ t) %⁺ [] = greater (∷-pred h t)
  [] %⁺ (h ∷ t) = less (∷-pred h t)
  (x ∷ xs) %⁺ (y ∷ ys) with xs %⁺ ys
  ... | greater gt = greater (addBit gt (x %f y))
  ... | less lt = less (addBit lt (y %f x))
  ... | equal = map-cmp (λ _ → []) (x %f y)

  succ : Bin⁺ → Bin⁺
  succ [] = zero ∷ []
  succ (zero ∷ t) = suc zero ∷ t
  succ (suc zero ∷ t) = zero ∷ succ t
  succ (suc (suc ()) ∷ t)
  
  succpred-id : ∀ x xs → succ (∷-pred x xs) ≡ x ∷ xs
  succpred-id zero [] = refl
  succpred-id zero (x ∷ xs) = cong (λ z → zero ∷ z) (succpred-id x xs)
  succpred-id (suc zero) xs = refl
  succpred-id (suc (suc ())) xs

  _-_ : Bin → Bin → Bin
  x - y with x -? y
  ... | positive (greater d _) = d 1#
  ... | equal _ = 0#
  ... | negative _ = 0#

  open import Data.Bin.Bijection using (toℕ-inj; fromToℕ-inverse; fromℕ-inj)

  open import Data.Bin.Addition using (+-is-addition)

  suc-inj : ∀ {x y : ℕ} → Data.Nat.suc x ≡ suc y → x ≡ y
  suc-inj {x} .{x} refl = refl

  ℕ-+-inj₂ : ∀ z {a b} → Data.Nat._+_ z a ≡ Data.Nat._+_ z b → a ≡ b
  ℕ-+-inj₂ zero refl = refl
  ℕ-+-inj₂ (suc n) eq = ℕ-+-inj₂ n (suc-inj eq)

  +-inj₂ : ∀ z {a b} → z + a ≡ z + b → a ≡ b
  +-inj₂ z {a} {b} z+a≡z+b = toℕ-inj ( ℕ-+-inj₂ (toℕ z) (sym (+-is-addition z a) ⟨ trans ⟩ cong toℕ z+a≡z+b ⟨ trans ⟩ +-is-addition z b) )
 
  nat-+zz : ∀ a b → Data.Nat._+_ a b ≡ 0 → a ≡ 0
  nat-+zz zero b _ = refl
  nat-+zz (suc _) b ()

  +zz : ∀ a b → a + b ≡ 0# → a ≡ 0#
  +zz a b eq = toℕ-inj (nat-+zz (toℕ a) (toℕ b) (sym (+-is-addition a b) ⟨ trans ⟩ cong toℕ eq))

  minus-elim : ∀ x z → z + x - z ≡ x
  minus-elim x z with (z + x -? z)
  ... | positive (greater d z+d=z+x) = +-inj₂ z z+d=z+x
  ... | equal z+x≡z = +-inj₂ z (identityʳ z ⟨ trans ⟩ sym z+x≡z)
  ... | negative (greater d z+x+d≡z) = sym (+zz x (d 1#) (+-inj₂ z
         ( sym (+-assoc z x (d 1#)) ⟨ trans ⟩ z+x+d≡z ⟨ trans ⟩ sym (identityʳ z))))
  
  import Data.Bin.NatHelpers

  x≮z→x≡z+y : ∀ {x z} → ¬ x < z → ∃ λ y → x ≡ z + y
  x≮z→x≡z+y {x} {z} x≮z = case
    Data.Bin.NatHelpers.x≮z→x≡z+y (λ toℕ-leq → x≮z (less toℕ-leq))
    of λ { (y , eq) →  fromℕ y , toℕ-inj (
    begin
     toℕ x
      ≡⟨ eq ⟩
     toℕ z ℕ+ y
      ≡⟨ cong (λ q → toℕ z ℕ+ q) (fromℕ-inj (sym (fromToℕ-inverse (fromℕ y)))) ⟩
     toℕ z ℕ+ toℕ (fromℕ y)
      ≡⟨ sym (+-is-addition z (fromℕ y)) ⟩
     toℕ (z + fromℕ y)
    ∎) }
    

  -+-elim' : ∀ {x z} → ¬ x < z → x - z + z ≡ x
  -+-elim' {x} {z} x≮z = case x≮z→x≡z+y x≮z of
    λ { (y , refl) →  
   begin
    z + y - z + z
     ≡⟨ cong (λ q → q + z) (minus-elim y z)⟩
    y + z
     ≡⟨ +-comm y z ⟩
    z + y
   ∎ }
