module Data.Bin.Addition where

  open import Data.List using ([]; _∷_)
  open import Data.Bin using(addBits; addBitLists; addCarryToBitList)
  open import Relation.Binary.PropositionalEquality
  private
    module PropEq = Relation.Binary.PropositionalEquality
  open import Data.Fin using (zero; suc) renaming (toℕ to bitToℕ; _+_ to _+F_)
  open import Data.Fin.Props using (_+′_)
  open import Data.Digit using (fromDigits)
  open import Data.Product
  import Data.Nat.Properties

  open import Data.Bin.Bijection using (bijection)

  module Solving where

   open Relation.Binary.PropositionalEquality

   open ≡-Reasoning
   open import Algebra
--   open Algebra.Structures
   open CommutativeSemiring Data.Nat.Properties.commutativeSemiring hiding (sym; refl)

   open Data.Product

   open Data.Nat.Properties.SemiringSolver


   lem : ∀ {a b c as bs b' c' r} 
          → c' * 2 + b' ≡ c + a + b 
          → r ≡ c' + (as + bs) 
          → b' + r * 2 ≡ c + (a + as * 2 + (b + bs * 2))
   lem {a} {b} {c} {as} {bs} {b'} {c'} {r}
          eq1 eq2 =
     begin
      b' + r * 2
       ≡⟨ cong (λ x → b' + x * 2) eq2 ⟩
      b' + (c' + (as + bs))  * 2
       ≡⟨ cong (λ x → b' + x) (proj₂ distrib 2 c' (as + bs)) ⟩
      b' + (c' * 2 + (as + bs) * 2)
       ≡⟨ sym (+-assoc b' (c' * 2) ((as + bs) * 2)) ⟩
      b' + c' * 2 + (as + bs) * 2
       ≡⟨  +-cong (+-comm b' (c' * 2)) refl ⟩
      c' * 2 + b' + (as + bs) * 2
       ≡⟨  +-cong eq1 refl ⟩
      c + a + b + (as + bs) * 2
       ≡⟨ solve 5 (λ a b c as bs → 
            c :+ a :+ b :+ (as :+ bs) :* con 2
         := c :+ (a :+ as :* con 2 :+ (b :+ bs :* con 2))
           ) refl a b c as bs  ⟩
      c + (a + as * 2 + (b + bs * 2))
     ∎

  open import Data.Nat using () renaming (_+_ to _+_; _*_ to _*_)
  open Data.Bin using (toℕ; toBits)

  addBits-is-addition : ∀ {c a b} → bitToℕ (proj₁ (addBits c a b)) * 2 + bitToℕ (proj₂ (addBits c a b)) ≡ bitToℕ c + bitToℕ a + bitToℕ b
  -- Brute force!!! (LOL)
  addBits-is-addition {zero} {zero} {zero} = refl
  addBits-is-addition {zero} {zero} {suc zero} = refl
  addBits-is-addition {zero} {suc zero} {zero} = refl
  addBits-is-addition {zero} {suc zero} {suc zero} = refl
  addBits-is-addition {suc zero} {zero} {zero} = refl
  addBits-is-addition {suc zero} {zero} {suc zero} = refl
  addBits-is-addition {suc zero} {suc zero} {zero} = refl
  addBits-is-addition {suc zero} {suc zero} {suc zero} = refl
  addBits-is-addition {suc (suc ())}
  addBits-is-addition {_} {suc (suc ())}
  addBits-is-addition {_} {_} {suc (suc ())}

  addCarryToBitLists-is-addition : ∀ c b → fromDigits (addCarryToBitList c b) ≡ bitToℕ c + fromDigits b
  addCarryToBitLists-is-addition zero _ = refl
  addCarryToBitLists-is-addition (suc zero) [] = refl
  addCarryToBitLists-is-addition (suc zero) (zero ∷ t) = refl
  addCarryToBitLists-is-addition (suc zero) (suc zero ∷ t) = cong (λ x → x * 2) (addCarryToBitLists-is-addition (suc zero) t)
  addCarryToBitLists-is-addition (suc (suc ())) _
  addCarryToBitLists-is-addition _ ((suc (suc ())) ∷ _)

  open import Data.Nat.Properties using (isCommutativeSemiring)
  open import Algebra.Structures 
     using (module IsCommutativeSemiring; 
            module IsCommutativeMonoid)
  open IsCommutativeSemiring isCommutativeSemiring 
     using (+-isCommutativeMonoid)
  open IsCommutativeMonoid +-isCommutativeMonoid using (identity; comm) renaming (∙-cong to +-cong)

  addBitLists-is-addition : ∀ c a b → fromDigits (addBitLists c a b) ≡ bitToℕ c + (fromDigits a + fromDigits b)
  addBitLists-is-addition c [] b = addCarryToBitLists-is-addition c b
  addBitLists-is-addition c (a ∷ as) [] = trans (addCarryToBitLists-is-addition c (a ∷ as)) (+-cong {bitToℕ c} refl (sym (proj₂ identity (fromDigits (a ∷ as)))))
  addBitLists-is-addition c (a ∷ as) (b ∷ bs) with addBits c a b | addBits-is-addition {c} {a} {b}
  ... | (c' , b') | abia with addBitLists c' as bs | addBitLists-is-addition c' as bs
  ... | r | ria = Solving.lem {bitToℕ a} {bitToℕ b} {bitToℕ c} {fromDigits as} {fromDigits bs} {bitToℕ b'} {bitToℕ c'} abia ria 

  open import Data.Bin.Bijection using (fromBits-preserves-ℕ)
  +-is-addition : ∀ a b → toℕ (Data.Bin._+_ a b) ≡ toℕ a + toℕ b
  +-is-addition a b = trans (fromBits-preserves-ℕ (addBitLists zero (toBits a) (toBits b))) (addBitLists-is-addition zero as bs) where
    as = toBits a
    bs = toBits b

  import Algebra.Lifting
  open import Data.Nat using (ℕ)
  open import Data.Bin using (Bin; 0#)
  open import Algebra.Structures using (IsCommutativeMonoid)
  private module Lifting = Algebra.Lifting (PropEq.setoid ℕ) (PropEq.setoid Bin) bijection

  is-commutativeMonoid : IsCommutativeMonoid _≡_ Data.Bin._+_ 0#
  is-commutativeMonoid = lift-isCommutativeMonoid 0 +-isCommutativeMonoid
   where
     open Lifting.WithOp₂ _+_ Data.Bin._+_ +-is-addition
