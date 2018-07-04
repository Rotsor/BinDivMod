{-                                                            
This file is a part of the library  Binary-3.1.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.  

Binary-3.1  is free software: you can redistribute it and/or modify it 
under the terms of the GNU General Public License.
See  license.txt.
-}

module GCD where

open import Function                   using (flip; _∘_; _$_; case_of_; const)
open import Algebra.FunctionProperties using (Op₂)
open import Relation.Nullary           using (Dec; yes; no)
open import Relation.Binary            using (Tri)
open import Relation.Binary.PropositionalEquality as PE 
                            using (_≡_; subst; cong; cong₂; refl; sym; trans)
open PE.≡-Reasoning renaming (begin_ to begin≡_; _∎ to _end≡)
open import Data.Empty   using (⊥-elim)
open import Data.Sum     using (inj₁)
open import Data.Product using (proj₁; _,_)
open import Data.List    using ([]; _∷_; _∷ʳ_) renaming (length to ln)
open import Data.Nat using (ℕ; z≤n; s≤s) 
                 renaming (suc to 1+_; _+_ to _+n_; _≤_ to _≤n_; _<_ to _<n_)
open import Data.Nat.Properties as NatP using () 
            renaming (≤-refl to ≤n-refl; +-mono-≤ to +n-mono-≤; 
                      +-comm to +n-comm; module ≤-Reasoning to ≤n-Reasoning
                     )
open ≤n-Reasoning using () renaming (begin_ to ≤nBegin_; _∎ to _≤nEnd;
                                     _≡⟨_⟩_ to _≡≤n[_]_; _≤⟨_⟩_ to _≤n[_]_)


-- of application ---
open import LtReasoning using (module InequalityReasoning)  -- by U. Norell
import NatProp0
open import List0 using (length-xs:x)
open import Bin0  using (Bin; _∣_; suc; _+_; _*_; _*2; _<_; _>_; _≤_; 0b; 1b)
                  renaming (1bin to 1'; 2bin to 2')
open import Bin1 using (<-cmp; bs1≢0; ∣_∣; _<?_; _≤?_; ≤-refl; ≤-reflexive; 
                        <-trans; ≤-trans; <-≤-trans; ≤-<-trans; <⇒≱; ≮⇒≥; ≰⇒>;
                                              1≤|x|; ∣_∣-mono-≤; *2≗2bin*) 
open import Bin2 using (0+; +0; +-comm)
open import Bin3 using (*0; *1; ∣x⇒∣y*x; ∣+; *-assoc; *-comm; *2≗*2bin; *2≗+)
open import Bin4 using (<⇒suc≤; +-mono-≤; +-mono-≤-<; *-mono-≤; x≤y+x)
open import Minus  using (_∸_; *-lDistrib-∸; [x+y]∸y≡x)
open import DivMod using (DivMod; divMod; result)



--****************************************************************************
record GCD (a b : Bin) : Set
       where
       constructor gcd′

       field  proper   : Bin             -- proper gcd   
              divides₁ : proper ∣ a
              divides₂ : proper ∣ b
              greatest : ∀ {d} → (d ∣ a) → (d ∣ b) → (d ∣ proper)


swapGCD :  {a b : Bin} → GCD a b → GCD b a
swapGCD (gcd′ g g∣a g∣b maxg) =  gcd′ g g∣b g∣a (\{d} → flip (maxg {d}))

------------------------------------------------------------------------------
open Bin
open Tri

open InequalityReasoning _<_ _≤_ (\{x y} → ≤-reflexive {x} {y})
                                 (\{x y z} → <-trans   {x} {y} {z})
                                 (\{x y z} → ≤-trans   {x} {y} {z})
                                 (\{x y z} → <-≤-trans {x} {y} {z})
                                 (\{x y z} → ≤-<-trans {x} {y} {z})


------------------------------------------------------------------------------
gcd : (a b : Bin) → GCD a b 

{- METHOD.
 The Euclidean algorithm:  recurse  gcd x y = gcd y r,  r = rem x y,
                                                        until y ≡ 0.
 The gcd function applies  liftGCD  to restore  gcd x y  from  gcd y r.

 The simple cases of  y ≡ 0,  rem x y ≡ 0,  quot x y ≡ 0  are done separately.
   
 But it is also provided a termination proof.
 It is based on the counter initiated as  cnt = |x| + |y|  
 - sum of bit length for x and y.  It holds  |x| + |y| ≤ cnt  during the 
 evaluation, and with each step, the value of  |x| + |y|  is decreased.
 This inequality is proved as follows.
 At each iteration, (x, y) is changed to (y, r),  r = rem x y,  q = quot x y. 
 The proof for  
                   |y| + |r| < |x| + |y|    (I)
 is as follows.
 If  y*2 ≤ x,  then it is proved   |y| < |x|.
 Together with  r < y  and  |r| ≤ |y|,  this proves  (I).
   
 If  y^2 > x,  then it is proved  q = 1,  r*2 < x,  |r| < |x|.  
 And this implies (I).
-}

gcd a b =  case a <? b  -- put maximal argument ahead
           of \ 
           { (yes a<b) → swapGCD $ gc b a (inj₁ a<b) (∣ b ∣ +n ∣ a ∣) ≤n-refl
           ; (no a≮b)  → gc a b (≮⇒≥ a≮b) (∣ a ∣ +n ∣ b ∣) ≤n-refl
           }
  where
  gc : (x y : Bin) → y ≤ x → (cnt : ℕ) → ∣ x ∣ +n ∣ y ∣ ≤n cnt → GCD x y 

  gc x 0#      _ _ _      =  gcd′ x (1' , *1 x) (0# , *0 x) (\ d∣x _ → d∣x)

  gc x (bs 1#) _ 0 oSum≤0 =  ⊥-elim (NatProp0.≤⇒≯ oSum≤0 0<oSum)
       where
       0<oSum :  0 <n ∣ x ∣ +n ∣ bs 1# ∣
       0<oSum =
         ≤nBegin 1                   ≤n[ s≤s z≤n ]
                 2                   ≤n[ +n-mono-≤ (1≤|x| x) (1≤|x| (bs 1#)) ]
                 ∣ x ∣ +n ∣ bs 1# ∣
         ≤nEnd

  gc x (bs 1#) y≤x (1+ cnt) |x|+|y|≤1+cnt = 
                                      aux (y*2 ≤? x) (divMod x y (bs1≢0 bs)) 
    where
    bs1 = bs 1#;   y       = bs1            -- the divisor
    y*2 = y *2;    |y|≤|x| = ∣_∣-mono-≤ y≤x

    --------------------------------------------------------------------------
    liftGCD :  (res : DivMod x y) → GCD y (DivMod.remainder res) → GCD x y
    liftGCD (result q r x≡r+q*y r<y)
            (gcd′ g (q₁ , gq₁≡y) (q₂ , gq₂≡r) maximality) = 
                                      gcd′ g g∣x g∣y (\ {d} → maximality' {d})
        where
        q*y = q * y
        g∣y = (q₁ , gq₁≡y)

        g∣r : g ∣ r
        g∣r = (q₂ , gq₂≡r)

        g∣q*y :  g ∣ q*y 
        g∣q*y =  ∣x⇒∣y*x {g} y q g∣y

        g∣r+q*y :  g ∣ (r + q*y)
        g∣r+q*y =  ∣+ {g} r q*y g∣r g∣q*y
 
        g∣x :  g ∣ x
        g∣x =  subst (g ∣_) (sym x≡r+q*y) g∣r+q*y

        x-q*y≡r :  x ∸ q*y ≡ r 
        x-q*y≡r =  begin≡ x ∸ q*y            ≡⟨ cong (_∸ q*y) x≡r+q*y ⟩ 
                          (r + q*y) ∸ q*y    ≡⟨ [x+y]∸y≡x r q*y ⟩ 
                          r                   
                   end≡

        maximality' :  ∀ {d} → d ∣ x → d ∣ y → d ∣ g
        maximality' {d} (s , ds≡x) (t , dt≡y) =  maximality {d} d∣y d∣r  
          where
          d∣y : d ∣ y 
          d∣y = (t , dt≡y) 

          tq = t * q
        
          d[s-tq]≡r :  d * (s ∸ tq) ≡ r
          d[s-tq]≡r = 
              begin≡ 
                d * (s ∸ tq)         ≡⟨ *-lDistrib-∸ d s tq ⟩
                (d * s) ∸ (d * tq)   ≡⟨ cong₂ _∸_ ds≡x (sym $ *-assoc d t q) ⟩
                x ∸ (d * t) * q      ≡⟨ cong ((x ∸_) ∘ (_* q)) dt≡y ⟩
                x ∸ y * q            ≡⟨ cong (x ∸_) (*-comm y q) ⟩
                x ∸ q * y            ≡⟨ x-q*y≡r ⟩
                r
              end≡ 

          d∣r :  d ∣ r
          d∣r =  ((s ∸ tq) , d[s-tq]≡r) 

    --------------------------------------------------------------------------
    aux :  Dec (y*2 ≤ x) → DivMod x y → GCD x y

    aux _  (result 0# r x≡r+0*y r<y) =  ⊥-elim (<⇒≱ x<y y≤x)
                                        where
                                        x<y = begin x           ≡[ x≡r+0*y ]
                                                    r + 0# * y  ≡[ refl ]
                                                    r + 0#      ≡[ +0 r ]
                                                    r           <[ r<y ]
                                                    y
                                              ∎

    aux _ (result q 0# x≡0+q*y 0<y) =            -- here  gcd x y = y
                               gcd′ y (q , yq≡x) (1' , *1 y) (\ _ d∣y → d∣y)
                               where
                               yq≡x = begin≡ y * q       ≡⟨ *-comm y q ⟩
                                             q * y       ≡⟨ sym (0+ (q * y)) ⟩
                                             0# + q * y  ≡⟨ sym x≡0+q*y ⟩
                                             x
                                      end≡

    aux (yes y*2≤x) (result q (rs 1#) x≡r+q*y r<y) =  -- here |y| < |x|

                            liftGCD (result q (rs 1#) x≡r+q*y r<y)
                                    (gc y r (inj₁ r<y) cnt |y|+|r|≤cnt)
      where
      r = rs 1#;    |r|≤|y| =  ∣_∣-mono-≤ {r} {y} (inj₁ r<y) 
 
      |y|<|x| =  ≤nBegin 1+ ∣ y ∣   ≡≤n[ refl ] 
                         ∣ y *2 ∣    ≤n[ ∣_∣-mono-≤ y*2≤x ]
                         ∣ x ∣ 
                 ≤nEnd  
 
      |y|+|r|≤cnt :  ∣ y ∣ +n ∣ r ∣ ≤n cnt
      |y|+|r|≤cnt = 
         NatP.pred-mono $
         ≤nBegin 1+ (∣ y ∣ +n ∣ r ∣)    ≤n[ NatP.+-mono-<-≤ |y|<|x| |r|≤|y| ]
                 ∣ x ∣ +n ∣ y ∣         ≤n[ |x|+|y|≤1+cnt ] 
                 1+ cnt
         ≤nEnd  


    aux (no y*2≰x) (result ((c ∷ cs) 1#) r x≡r+q*y r<y) = ⊥-elim (y*2≰x y*2≤x)
        where
        q     = (c ∷ cs) 1# 
        1<|q| = ≤nBegin 2               ≤n[ NatP.m≤m+n 2 (ln cs) ]
                        2 +n (ln cs)   ≡≤n[ sym (cong 1+_ (length-xs:x 1b cs))
                                          ]
                        ∣ q ∣ 
                ≤nEnd

        1<q   = inj₁ 1<|q|
        2≤q   = <⇒suc≤ {1'} {q} 1<q
        y*2≤x = begin y *2         ≤[ x≤y+x (y *2) r ]
                      r + y *2     ≡[ cong (r +_) (*2≗2bin* y) ]
                      r + 2' * y   ≤[ +-mono-≤ (≤-refl {r}) 
                                               (*-mono-≤ 2≤q (≤-refl {y}) ) ]  
                      r + q * y    ≡[ sym x≡r+q*y ]
                      x
                ∎

    aux (no y*2≰x) (result ([] 1#) (rs 1#) x≡r+1*y r<y) =    -- here |r| < |x|
                                
                               liftGCD (result ([] 1#) (rs 1#) x≡r+1*y r<y)
                                       (gc y r (inj₁ r<y) cnt |y|+|r|≤cnt)
      where
      q = 1';  r = rs 1#;  x<y*2 = ≰⇒> y*2≰x 

      r*2<x =  begin 
                 r *2         ≡[ *2≗+ r ]
                 r + r        <[ +-mono-≤-< {r} {r} {r} {y} (≤-refl {r}) r<y ]
                 r + y        ≡[ refl ]
                 r + 1' * y   ≡[ sym x≡r+1*y ]
                 x
               ∎

      |r|<|x| =  ≤nBegin 1+ ∣ r ∣   ≡≤n[ refl ]   
                         ∣ r *2 ∣    ≤n[ ∣_∣-mono-≤ {r *2} {x} (inj₁ r*2<x) ]
                         ∣ x ∣ 
                 ≤nEnd 

      |y|+|r|≤cnt = 
        NatP.pred-mono $
        ≤nBegin 
          1+ (∣ y ∣ +n ∣ r ∣)   ≡≤n[ cong 1+_ (+n-comm ∣ y ∣ ∣ r ∣) ]
          1+ (∣ r ∣ +n ∣ y ∣)    ≤n[ NatP.+-mono-<-≤ |r|<|x| (≤n-refl {∣ y ∣}) 
                                   ]
          ∣ x ∣ +n ∣ y ∣         ≤n[ |x|+|y|≤1+cnt ] 
          1+ cnt
        ≤nEnd        


----------------------------
gcd! : Op₂ Bin
gcd! x =  GCD.proper ∘ gcd x