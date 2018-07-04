{-                                                            
This file is a part of the library  Binary-3.0.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.  

Binary-3.0  is free software: you can redistribute it and/or modify it 
under the terms of the GNU General Public License.
See  license.txt.
-}

module Bin3a where        -- Algebra Instances for _*_ on Bin.

open import Level   using () renaming (zero to 0ℓ)
open import Algebra using (Semigroup; Monoid; CommutativeMonoid; Semiring;
                                                         CommutativeSemiring) 
open import Algebra.Structures using 
     (IsSemigroup; IsMonoid; IsCommutativeMonoid; IsSemiring; 
      IsSemiringWithoutAnnihilatingZero; IsCommutativeSemiring 
     )
open import Relation.Binary.PropositionalEquality 
                                       using (_≡_; refl; isEquivalence; cong₂)
open import Data.Product using (_,_)

-- of application ---
open import Bin0  using (Bin; _+_; _*_; 0#; 1bin)
open import Bin2a using () 
                  renaming (isCommutativeMonoid to +-isCommutativeMonoid)
open import Bin3 using (*0; *1; *-assoc; *-comm; rDistrib; distrib)



--****************************************************************************
open Bin

isSemigroup : IsSemigroup _≡_ _*_
isSemigroup = record{ isEquivalence = isEquivalence
                    ; assoc         = *-assoc
                    ; ∙-cong        = cong₂ _*_ }

semigroup : Semigroup 0ℓ 0ℓ  
semigroup = 
  record{ Carrier = Bin;  _≈_ = _≡_;  _∙_ = _*_;  isSemigroup = isSemigroup }

------------------------------------------------------------------------------
isMonoid : IsMonoid _≡_ _*_ 1bin
isMonoid = record{ isSemigroup = isSemigroup;  
                   identity    = ((\x → refl {x = x}) , *1) }

monoid : Monoid 0ℓ 0ℓ  
monoid = record{ Carrier = Bin; 
                 _≈_ = _≡_;   _∙_ = _*_;   ε = 1bin;   isMonoid = isMonoid }


isCommutativeMonoid : IsCommutativeMonoid _≡_ _*_ 1bin
isCommutativeMonoid =  record{ isSemigroup = isSemigroup
                             ; identityˡ   = (\_ → refl)
                             ; comm        = *-comm }

commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
commutativeMonoid = record{ Carrier = Bin;  _≈_ = _≡_;  _∙_ = _*_;  ε = 1bin; 
                            isCommutativeMonoid = isCommutativeMonoid }

------------------------------------------------------------------------------
isSemiringWithoutAnnihilatingZero : 
                         IsSemiringWithoutAnnihilatingZero _≡_ _+_ _*_ 0# 1bin
isSemiringWithoutAnnihilatingZero =
  record{ +-isCommutativeMonoid = +-isCommutativeMonoid
        ; *-isMonoid            = isMonoid 
        ; distrib               = distrib
        }

isSemiring : IsSemiring _≡_ _+_ _*_ 0# 1bin 
isSemiring = 
  record{ isSemiringWithoutAnnihilatingZero = 
                                            isSemiringWithoutAnnihilatingZero
        ; zero = ((\x → refl {x = 0#}) , *0)
        }
        
semiring : Semiring 0ℓ 0ℓ  
semiring = record{ Carrier    = Bin;         _≈_ = _≡_;    _+_ = _+_;  
                   _*_        = _*_;         0#  = 0#;     1# = 1bin;
                   isSemiring = isSemiring
                 }


isCommutativeSemiring : IsCommutativeSemiring _≡_ _+_ _*_ 0# 1bin
isCommutativeSemiring =
             record{ +-isCommutativeMonoid = +-isCommutativeMonoid 
                   ; *-isCommutativeMonoid = isCommutativeMonoid 
                   ; distribʳ              = rDistrib
                   ; zeroˡ                 = (\x → refl {x = 0#}) 
                   }

commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
commutativeSemiring = 
           record{ Carrier = Bin; 
                   _≈_ = _≡_;  _+_ = _+_;  _*_ = _*_;  0# = 0#;  1# = 1bin;
                   isCommutativeSemiring = isCommutativeSemiring 
                 }




