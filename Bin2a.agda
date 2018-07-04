{-                                                            
This file is a part of the library  Binary-3.1.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.  

Binary-3.1  is free software: you can redistribute it and/or modify it 
under the terms of the GNU General Public License.
See  license.txt.
-}

module Bin2a where        -- Algebra Instances for _+_ on Bin.

open import Level   using () renaming (zero to 0ℓ)
open import Algebra using (Semigroup; Monoid; CommutativeMonoid)
open import Algebra.Structures using (IsSemigroup; IsMonoid;
                                                   IsCommutativeMonoid)
open import Relation.Binary.PropositionalEquality 
                                         using (_≡_; cong₂; isEquivalence)
open import Data.Product using (_,_)

-- of application ---
open import Bin0 using (Bin; _+_)
open import Bin2 using (0+; +0; +-assoc; +-comm)



--****************************************************************************
open Bin

isSemigroup : IsSemigroup _≡_ _+_
isSemigroup = record{ isEquivalence = isEquivalence
                    ; assoc         = +-assoc
                    ; ∙-cong        = cong₂ _+_ }

semigroup : Semigroup 0ℓ 0ℓ  
semigroup = 
  record{ Carrier = Bin;  _≈_ = _≡_;  _∙_ = _+_;  isSemigroup = isSemigroup }


------------------------------------------------------------------------------
isMonoid : IsMonoid _≡_ _+_ 0#
isMonoid = record{ isSemigroup = isSemigroup;  identity = (0+ , +0) }

monoid : Monoid 0ℓ 0ℓ  
monoid = record{ Carrier = Bin; 
                 _≈_ = _≡_;   _∙_ = _+_;   ε = 0#;   isMonoid = isMonoid }


isCommutativeMonoid : IsCommutativeMonoid _≡_ _+_ 0#
isCommutativeMonoid =  record{ isSemigroup = isSemigroup
                             ; identityˡ   = 0+
                             ; comm        = +-comm }

commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
commutativeMonoid = record{ Carrier = Bin;  _≈_ = _≡_;   _∙_ = _+_;   ε = 0#; 
                            isCommutativeMonoid = isCommutativeMonoid }



