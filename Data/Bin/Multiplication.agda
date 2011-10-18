
import Relation.Binary.PropositionalEquality
module Data.Bin.Multiplication where
  private module PropEq = Relation.Binary.PropositionalEquality

  module ℕ-lemmas where
    open import Data.Nat
    open import Data.Nat.Properties
    open import Relation.Binary.PropositionalEquality
    open SemiringSolver

    *-2-3-comm : ∀ x y z → x * y * z ≡ x * z * y
    *-2-3-comm x y z = solve 3 (λ x y z → x :* y :* z := x :* z :* y) refl x y z

    n+x≡0→n≡0 : ∀ {n x} → n + x ≡ 0 → n ≡ 0
    n+x≡0→n≡0 {zero} = λ _ → refl
    n+x≡0→n≡0 {suc _} = λ ()

    distribʳ : ∀ a b c → (a + b) * c ≡ a * c + b * c
    distribʳ a b c = solve 3 (λ a b c → (a :+ b) :* c := a :* c :+ b :* c) refl a b c



  open PropEq using (_≡_; Inspect; inspect; _with-≡_; cong; cong₂; trans; sym)
  open import Data.Bin using (_*2; toℕ; 0#; _1#; Bin; pred; _*_; _+_)
  open import Data.Nat using (ℕ; zero; suc)
                     renaming (_*_ to _ℕ*_; _+_ to _ℕ+_)
  open import Data.Nat.Properties using (isCommutativeSemiring)
  open import Algebra.Structures 
     using (module IsCommutativeSemiring; 
            module IsCommutativeMonoid)
  open IsCommutativeSemiring isCommutativeSemiring
     using (+-isCommutativeMonoid; *-isCommutativeMonoid)

  open import Data.Product

  import Data.Bin.BitListBijection
  open Data.Bin.BitListBijection.DigitInj using (*-inj₂)

  open import Relation.Nullary
  open import Data.Fin using (zero; suc) renaming (toℕ to bitToℕ)
  open import Data.Digit using (Bit)
  open import Data.List using (List; _∷_; [])
  open import Data.Bin.Utils

  open import Data.Bin.Bijection using (toℕ-inj)
  import Relation.Binary.PropositionalEquality
  open Relation.Binary.PropositionalEquality.≡-Reasoning


  import Data.Bin.Addition
  open Data.Bin.Addition using (+-is-addition)
  module B+ICM = IsCommutativeMonoid Data.Bin.Addition.is-commutativeMonoid
  open B+ICM using () renaming (identity to +-identity; ∙-cong to +-cong)

  *2-is-*2 : ∀ x → toℕ (x *2) ≡ toℕ x ℕ* 2
  *2-is-*2 0# = PropEq.refl
  *2-is-*2 (bs 1#) = PropEq.refl

  bitToX-≡ : ∀ x → bitToℕ x ≡ toℕ (bitToBin x)
  bitToX-≡ zero = PropEq.refl
  bitToX-≡ (suc zero) = PropEq.refl
  bitToX-≡ (suc (suc ()))

  ∷1#-interpretation : ∀ (b : Bit) (bs : List Bit) → ((b ∷ bs) 1#) ≡ bitToBin b + (bs 1#) *2
  ∷1#-interpretation b bs = toℕ-inj (
   begin
    toℕ ((b ∷ bs) 1#)
     ≡⟨ PropEq.refl ⟩
    bitToℕ b ℕ+ toℕ (bs 1#) ℕ* 2
     ≡⟨ cong₂ _ℕ+_ (bitToX-≡ b) (sym (*2-is-*2 (bs 1#))) ⟩
    toℕ (bitToBin b) ℕ+ toℕ ((bs 1#) *2)
     ≡⟨ sym (+-is-addition (bitToBin b) ((bs 1#) *2)) ⟩
    toℕ (bitToBin b + (bs 1#) *2)
   ∎)
  
  open import Function using (_⟨_⟩_)

  multBit : Bit → Bin → Bin
  multBit zero _ = 0#
  multBit (suc zero) n = n
  multBit (suc (suc ())) _

  n+x≡0→n≡0 : ∀ {n x} → n + x ≡ 0# → n ≡ 0#
  n+x≡0→n≡0 {n} {x} n+x≡0 = toℕ-inj (ℕ-lemmas.n+x≡0→n≡0 ((sym (+-is-addition n x)) ⟨ trans ⟩ cong toℕ n+x≡0))

  1+*n≡0→n≡0 : ∀ {l} n → l 1# * n ≡ 0# → n ≡ 0#
  1+*n≡0→n≡0 {[]} n eq = eq
  1+*n≡0→n≡0 {h ∷ t} n eq with inspect (t 1# * n)
  1+*n≡0→n≡0 {h ∷ t} n _ | 0# with-≡ eq = 1+*n≡0→n≡0 {t} n eq
  1+*n≡0→n≡0 {zero ∷ t} n eq | (l 1#) with-≡ eq2 rewrite eq2 with eq
  ... | ()
  1+*n≡0→n≡0 {suc zero ∷ t} n eq | (l 1#) with-≡ eq2 rewrite eq2 = n+x≡0→n≡0 {n} {(zero ∷ l) 1#} eq
  1+*n≡0→n≡0 {suc (suc ()) ∷ t} n eq | _

  simplify-mult : ∀ x xs n → (x ∷ xs) 1# * n ≡ multBit x n + (xs 1# * n) *2
  simplify-mult x xs n with inspect (xs 1# * n)
  simplify-mult zero xs n | 0# with-≡ ≡ rewrite ≡ = PropEq.refl
  simplify-mult (suc zero) xs n | 0# with-≡ ≡ rewrite ≡ | 1+*n≡0→n≡0 {xs} n ≡ = PropEq.refl
  simplify-mult zero xs n | (xs' 1#)  with-≡ ≡ rewrite ≡ =
    begin
      (zero ∷ xs') 1#
        ≡⟨ PropEq.refl ⟩
      (xs' 1#) *2
        ≡⟨ B+ICM.sym ( B+ICM.identityˡ ((xs' 1#) *2)) ⟩
      0# + (xs' 1#) *2
        ≡⟨ PropEq.refl ⟩
      multBit zero n + (xs' 1#) *2
    ∎
  simplify-mult (suc zero) xs n | (xs' 1#)  with-≡ ≡ rewrite ≡ =
    begin
      n + (zero ∷ xs') 1#
        ≡⟨ PropEq.refl ⟩
      multBit (suc zero) n + (xs' 1#) *2
    ∎
  simplify-mult (suc (suc ())) xs n | _

  _*-def'_ : ℕ → Bin → Bin
  zero *-def' y = 0#
  (suc x) *-def' y = y + (x *-def' y)
  
  _*-def_ : Bin → Bin → Bin
  x *-def y = (toℕ x) *-def' y
  infixl 7 _*-def_

  *-def'-is-* : ∀ m n → toℕ (m *-def' n) ≡ m ℕ* toℕ n
  *-def'-is-* zero n = PropEq.refl
  *-def'-is-* (suc m) n = +-is-addition  n ( m *-def' n) ⟨ trans ⟩ cong (_ℕ+_ (toℕ n)) (*-def'-is-* m n)

  *-def-is-* : ∀ m n → toℕ (m *-def n) ≡ toℕ m ℕ* toℕ n
  *-def-is-* m = *-def'-is-* (toℕ m)

  *-def-*2-comm : ∀ x y → (x *-def y) *2 ≡ x *2 *-def y
  *-def-*2-comm x y = toℕ-inj (
    begin
     toℕ ((x *-def y) *2)
      ≡⟨ *2-is-*2 (x *-def y) ⟩
     toℕ (x *-def y) ℕ* 2
      ≡⟨ cong (λ x → x ℕ* 2) (*-def-is-* x y) ⟩
     toℕ x ℕ* toℕ y ℕ* 2
      ≡⟨ ℕ-lemmas.*-2-3-comm (toℕ x) (toℕ y) 2 ⟩
     toℕ x ℕ* 2 ℕ* toℕ y
      ≡⟨ cong (λ x → x ℕ* toℕ y) (sym (*2-is-*2 x)) ⟩
     toℕ (x *2) ℕ* toℕ y
      ≡⟨ sym (*-def-is-* (x *2) y) ⟩
     toℕ (x *2 *-def y)
    ∎)

  multbit-is-*-def : ∀ c x → multBit c x ≡ bitToBin c *-def x
  multbit-is-*-def zero x = PropEq.refl
  multbit-is-*-def (suc zero) x = sym (proj₂ +-identity x)
  multbit-is-*-def (suc (suc ())) x

  *-def-distribʳ : ∀ a b c → (a + b) *-def c ≡ a *-def c + b *-def c
  *-def-distribʳ a b c = toℕ-inj (
    begin
     toℕ ((a + b) *-def c)
      ≡⟨ *-def-is-* (a + b) c ⟩
     toℕ (a + b) ℕ* toℕ c
      ≡⟨ cong (λ x → x ℕ* toℕ c) (+-is-addition a b) ⟩
     (toℕ a ℕ+ toℕ b) ℕ* toℕ c
      ≡⟨ ℕ-lemmas.distribʳ (toℕ a) (toℕ b) (toℕ c) ⟩
     toℕ a ℕ* toℕ c ℕ+ toℕ b ℕ* toℕ c
      ≡⟨ cong₂ _ℕ+_ (kojo a) (kojo b) ⟩
     toℕ (a *-def c) ℕ+ toℕ (b *-def c)
      ≡⟨ sym (+-is-addition (a *-def c) (b *-def c)) ⟩
     toℕ (a *-def c + b *-def c)
    ∎
    ) where
     kojo : ∀ x → toℕ x ℕ* toℕ c ≡ toℕ (x *-def c)
     kojo x = sym (*-def-is-* x c)

  mutual
    *-is-*-def : ∀ m n → m * n ≡ m *-def n
    *-is-*-def 0# n = PropEq.refl
    *-is-*-def (l 1#) n = *-is-*-def-1# l n

    *-is-*-def-1# : ∀ l n → l 1# * n ≡ l 1# *-def n
    *-is-*-def-1# [] n = sym (proj₂ +-identity n)
    *-is-*-def-1# (x ∷ xs) n = *-is-*-def-∷ x xs n

    *-is-*-def-∷ : ∀ h t n → (h ∷ t) 1# * n ≡ ((h ∷ t) 1#) *-def n
    *-is-*-def-∷ h t n = 
     begin
      (h ∷ t) 1# * n
       ≡⟨ simplify-mult h t n  ⟩
      multBit h n + (t 1# * n) *2
       ≡⟨ +-cong (multbit-is-*-def h n) (cong (λ x → x *2) (*-is-*-def-1# t n) ⟨ trans ⟩ *-def-*2-comm (t 1#) n) ⟩
      bitToBin h *-def n + t 1# *2 *-def n
       ≡⟨ sym (*-def-distribʳ (bitToBin h) (t 1# *2) n) ⟩
      (bitToBin h + t 1# *2) *-def n
       ≡⟨ cong (λ x → x *-def n) (sym (∷1#-interpretation h t)) ⟩
      ((h ∷ t) 1#) *-def n
     ∎


  *-*2-comm : ∀ x y → (x * y) *2 ≡ x *2 * y
  *-*2-comm x y = cong _*2 (*-is-*-def x y) ⟨ trans ⟩ *-def-*2-comm x y ⟨ trans ⟩ sym (*-is-*-def (x *2) y)

  *-distribʳ : ∀ a b c → (a + b) * c ≡ a * c + b * c
  *-distribʳ a b c = 
                     *-is-*-def (a + b) c
           ⟨ trans ⟩ *-def-distribʳ a b c
           ⟨ trans ⟩ sym (cong₂ _+_ (*-is-*-def a c) (*-is-*-def b c))


  *-is-multiplication : ∀ a b → toℕ (a * b) ≡ toℕ a ℕ* toℕ b
  *-is-multiplication a b = cong toℕ (*-is-*-def a b) ⟨ trans ⟩ *-def-is-* a b