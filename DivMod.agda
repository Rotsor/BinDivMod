{-                                                            
This file is a part of the library  Binary-3.0.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.  

Binary-3.0  is free software: you can redistribute it and/or modify it 
under the terms of the GNU General Public License.
See  license.txt.
-}

module DivMod where

open import Function         using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary  using (Tri)
open import Relation.Binary.PropositionalEquality as PE 
                                      using (_≡_; _≢_; subst; refl; sym; cong)
open PE.≡-Reasoning
open import Data.Empty   using (⊥-elim)
open import Data.Sum     using (inj₁)
open import Data.Product using (proj₁)
open import Data.List    using ([]; _∷_; _∷ʳ_; _++_; replicate)
open import Data.Nat     using (ℕ; s≤s) renaming (suc to 1+_; _≤_ to _≤n_) 
open import Data.Nat.Properties as NatP using ()
            renaming (≤-refl to ≤n-refl; ≤-reflexive to ≤n-reflexive; 
                      ≤-trans to ≤n-trans; module ≤-Reasoning to ≤n-Reasoning)

open ≤n-Reasoning using () renaming (begin_ to ≤nBegin_; _∎ to _≤nEnd;
                                     _≡⟨_⟩_ to _≡≤n[_]_; _≤⟨_⟩_ to _≤n[_]_)

-- of application ---
import NatProp0 
open import Bin0 using (Bin; _<_; _>_; _≤_; _+_; _*_; 0b; 1b; 0#; shift)
                                                         renaming (1bin to 1')
open import Bin1 using (_≟_; <-cmp; ≢sym; ≢0⇒0<; ≮0; 0<bs1; ∣_∣; 1≤|x|; 1≤bs1;
                        ≤,≢⇒<; shift≗++; shiftWhile≤; shiftWhile≤′
                       )
open import Bin2  using (+0; 0+; +-comm; +-assoc)
open import Bin3  using (rDistrib; shift-e≗2^e*)
open import Minus using (_∸_; x+[y∸x]≡y; y≤x,y*2>x⇒|x∸y|<n|x|)




--****************************************************************************
open Bin

record DivMod (dividend divisor : Bin) : Set where
       constructor result
       field
         quotient    :  Bin
         remainder   :  Bin
         equality    :  dividend ≡ remainder + quotient * divisor
         rem<divisor :  remainder < divisor
--
-- Note that  divisor ≢ 0#  in  DivMod _ divisor.

open Tri 


divMod : (dividend dr : Bin) → dr ≢ 0# → DivMod dividend dr
{- 
 Division with remainder.
 dd  stands for dividend,  dr  stands for divisor.
 The counter of  ∣ dd ∣ = bitLength dd  is used below to prove termination.

 METHOD:  repeat  s = shift n dr  for certain n  and  dd ∸ s  in a loop.
 
 Evaluation cost:  O (|dd|^2).
-}

divMod ddd 0#       0≢0  =  ⊥-elim (0≢0 refl)
divMod ddd (bs' 1#) dr≢0 =  aux ddd ∣ ddd ∣ ≤n-refl  
  where
  dr = bs' 1#;   bs':1 = bs' ∷ʳ 1b

  aux :  (dividend : Bin) → (cnt : ℕ) → ∣ dividend ∣ ≤n cnt → 
                                                        DivMod dividend dr
  aux dd 0 |dd|≤0 =  ⊥-elim (NatProp0.<⇒≱ 1≤|dd| |dd|≤0)
                     where
                     1≤|dd| = 1≤|x| dd 

  aux 0# _        _       =  result 0# 0# 0≡0+0*dr (0<bs1 bs') 
                             where
                             0≡0+0*dr = begin 0#            ≡⟨ sym (0+ 0#) ⟩
                                              0# + 0#       ≡⟨ refl ⟩
                                              0# + 0# * dr 
                                        ∎

  aux ([] 1#) _ _ with dr ≟ 1'
  ... 
      | yes dr≡1 =  result 1' 0# 1≡0+1*dr (0<bs1 bs') 
                 where
                 1≡0+1*dr = begin 1'              ≡⟨ refl ⟩
                                  1' * 1'         ≡⟨ cong (1' *_) (sym dr≡1) ⟩
                                  1' * dr         ≡⟨ sym (0+ (1' * dr)) ⟩
                                  0# + (1' * dr) 
                            ∎

  ... | no dr≢1 =  result 0# 1' 1≡1+0*dr 1<dr  
                   where
                   1≡1+0*dr = sym (+0 1')
                   1≤dr     = 1≤bs1 bs'  
                   1<dr     = ≤,≢⇒< 1≤dr (≢sym dr≢1)


  aux ((b ∷ bs) 1#) (1+ cnt) |dd|≤1+cnt  with  <-cmp ((b ∷ bs) 1#) dr
  
  ... | tri< dd<dr _ _ =  result 0# dd dd≡dd+0*dr dd<dr 
                          where
                          dd         = (b ∷ bs) 1#
                          dd≡dd+0*dr = begin dd            ≡⟨ sym (+0 dd) ⟩
                                             dd + 0#       ≡⟨ refl ⟩
                                             dd + 0# * dr
                                       ∎
                   
  ... | tri≈ _ dd≡dr _ =  result 1' 0# dd≡0+1*dr 0<dr 
                     where
                     dd        =  (b ∷ bs) 1#
                     0<dr      =  ≢0⇒0< dr≢0
                     dd≡0+1*dr =  begin dd             ≡⟨ sym (0+ dd) ⟩
                                        0# + dd        ≡⟨ cong (0# +_) dd≡dr ⟩
                                        0# + dr        ≡⟨ refl ⟩ 
                                        0# + (1' * dr)
                                  ∎

  ... | tri> _ _ dr<dd = 
    let 
      -- Shift  dr  to make it (2^e * dr)  the closest order to  dd.
      -- Then   bitLength (dd ∸ shifted-dr) < bitLength dd.

      dd = (b ∷ bs) 1#;   bbs:1 = (b ∷ bs) ∷ʳ 1b

      (shiftWhile≤′ e zrs:dr≤dd dd<0zrs:dr) = 
                                         shiftWhile≤ bs' (b ∷ bs) (inj₁ dr<dd)
      zrs    = replicate e 0b
      zrs:dr = (zrs ++ bs') 1#
      2^e    = shift e 1'
      dd'    = dd ∸ zrs:dr  

      |dd'|<|dd| =  y≤x,y*2>x⇒|x∸y|<n|x| b bs zrs:dr zrs:dr≤dd dd<0zrs:dr
      |dd'|≤cnt  =  NatP.pred-mono (≤n-trans |dd'|<|dd| |dd|≤1+cnt)

      (result q' r dd'≡r+q'*dr r<dr) =  aux dd' cnt |dd'|≤cnt
                                       
      q     = 2^e + q' 
      q'*dr = q' * dr

      zrs:dr≡2^e*dr :  zrs:dr ≡ 2^e * dr
      zrs:dr≡2^e*dr =  begin zrs:dr       ≡⟨ sym (shift≗++ e bs') ⟩
                             shift e dr   ≡⟨ shift-e≗2^e* e dr ⟩
                             2^e * dr
                       ∎

      dd≡r+q*dr :  dd ≡ r + q * dr
      dd≡r+q*dr = 
        begin
          dd                          ≡⟨ sym (x+[y∸x]≡y zrs:dr≤dd) ⟩
          zrs:dr + (dd ∸ zrs:dr)      ≡⟨ cong (zrs:dr +_) dd'≡r+q'*dr ⟩
          zrs:dr + (r + q'*dr)        ≡⟨ cong (zrs:dr +_) (+-comm r q'*dr) ⟩
          zrs:dr + (q'*dr + r)        ≡⟨ sym (+-assoc zrs:dr q'*dr r) ⟩
          (zrs:dr + q'*dr) + r        ≡⟨ cong ((_+ r) ∘ (_+ q'*dr)) 
                                                        zrs:dr≡2^e*dr ⟩ 
          (2^e * dr + q'*dr) + r   ≡⟨ cong (_+ r) (sym (rDistrib dr 2^e q')) ⟩ 
          (2^e + q') * dr + r      ≡⟨ +-comm ((2^e + q') * dr) r ⟩
          r + q * dr
        ∎
    in
    result q r dd≡r+q*dr r<dr