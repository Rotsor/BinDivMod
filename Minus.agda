{-                                                            
This file is a part of the library  Binary-3.0.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.  

Binary-3.0  is free software: you can redistribute it and/or modify it 
under the terms of the GNU General Public License.
See  license.txt.
-}

{-# OPTIONS --termination-depth=2 #-}

module Minus where

open import Function using (id; _∘_; _$_; case_of_; const)
open import Algebra.FunctionProperties as FuncProp using (Op₂)
open import Relation.Nullary using (Dec; yes; no) 
open import Relation.Binary  using (Tri; _Preserves₂_⟶_⟶_) 
open import Relation.Binary.PropositionalEquality as PE 
                                         using (_≡_; _≢_; _≗_; subst; subst₂; 
                                                cong; cong₂; refl; sym; trans)
open PE.≡-Reasoning renaming (begin_ to begin≡_; _∎ to _end≡) 
open import Data.Empty   using (⊥-elim)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.List    using (List; []; _∷_; _∷ʳ_; [_]; map) 
                                                     renaming (length to ln) 
open import Data.Digit using (Bit; fromDigits)
open import Data.Nat using (s≤s) 
            renaming (suc to 1+_; pred to predN; _+_ to _+n_; _<_ to _<n_;
                      _>_ to _>n_; _≤_ to _≤n_; _*_ to _*n_; _∸_ to _∸n_
                     )
open import Data.Nat.Properties as NProp using (m≤m+n)
    renaming (+-comm to +n-comm; ∸-mono to ∸n-mono; 
              ≤-reflexive to ≤n-reflexive; module ≤-Reasoning to ≤n-Reasoning
             )
open ≤n-Reasoning using () renaming (begin_ to ≤nBegin_; _∎ to _≤nEnd;
                                     _≡⟨_⟩_ to _≡≤n[_]_; _≤⟨_⟩_ to _≤n[_]_)

-- of application ---
open import LtReasoning using (module InequalityReasoning)  -- by U. Norell
open import NatProp0    using (_≤n?_) 
open import List0 using (length-xs:x) 
open import Bin0  using (_←→_; Bin; 0b; ⊥b; 1b; _*2; 2^_; _∈_; _∈?_; fromBits;
                         suc; pred; toℕ; _<_; _>_; _≤_; _≥_; _+_; _*_
                        )
                  renaming (1bin to 1'; 2bin to 2')
open import Bin1 using 
     (0<bs1; 0≢bs1; 1<bbs1; *2≗2bin*; <-trans; <-irrefl; <-asym; <-cmp; _≤?_; 
      ≢sym; ≢0#⇒≡bs1; ≮0; 0≤; ≤⇒≯; <⇒≢; <⇒≱; >⇒≢; ≢0⇒0<; ≤-reflexive; ≤-refl; 
      ≤-trans; <-≤-trans; ≤-<-trans; ≰⇒>; ∣_∣; ∣_∣-mono-≤; 1∉bs⇒fromBits-bs≡0; 
      1∈bs⇒|fromBits-bs|≤|bs|; |2^n|≡1+n; fromBits-bbs<2^|bbs|
     )
open import Bin2 using (0+; +0; +-comm; +-assoc; pred∘suc; suc∘pred; 
                        suc∘pred-for>0; toℕ+homo; fromℕ+homo; suc-even1; 
                        fromℕ; toℕ∘fromℕ; fromℕ∘toℕ; module FP-Bin
                       )
open import Bin3 using (rDistrib; *2≗*2bin; *2≗+; *2-distrib; toℕ*homo;
                        fromℕ*homo; partHighest-2^; |pred-2^[1+n]|<|2^[1+n]|)
open import Bin4 using 
     (0<1+x; x<1+x; x<x+1; x≤x+y; x≤y+x; pred-mono-<; pred-mono-≤; suc-mono-<; 
      suc-mono-≤; toℕ-mono-≤; fromℕ-mono-≤; +-mono-≤; +-mono-≤-<; +-mono-<-≤; 
      *bs1-mono-<; *2-mono-≤; *2-mono-<; *-mono-≤; x<y⇒a+x*a≤y*a; +-lCancel; 
      +-rCancel; pred<; 0<2^; <⇒suc≤; suc≤⇒< 
     )



--****************************************************************************
-- Subtraction on Bin  (minus, _∸_),  with certain its properties. 

open Bin 

open InequalityReasoning _<_ _≤_ (\{x y} → ≤-reflexive {x} {y})
                                 (\{x y z} → <-trans   {x} {y} {z})
                                 (\{x y z} → ≤-trans   {x} {y} {z})
                                 (\{x y z} → <-≤-trans {x} {y} {z})
                                 (\{x y z} → ≤-<-trans {x} {y} {z})

module _ (c : Bit) (x y : Bin)
  where
  private c+y = (fromBits [ c ]) + y

  data MinusRes (d : Bin) :  Set
       where
       minuend< :  x < c+y → d ≡ 0# → MinusRes d
       minuend≡ :  x ≡ c+y → d ≡ 0# → MinusRes d
       minuend> :  x > c+y → (x ≡ c+y + d) → MinusRes d

------------------------------------------------------------------------------
minus :  (c : Bit) → (x y : Bin) → ∃ (\d → MinusRes c x y d)

minus ⊥b 
minus _ ((⊥b ∷ _) 1#) 
minus _ _             ((⊥b ∷ _) 1#) 

minus 0b 0#      0# =  (0# , minuend≡ (refl {x = 0#}) refl) 
minus 0b (bs 1#) 0# =  (bs1 , minuend> (0<bs1 bs) bs1≡0+0+bs1) 
      where
      bs1         = bs 1#
      bs1≡0+0+bs1 = begin≡ bs1              ≡⟨ sym (0+ bs1) ⟩
                           0# + bs1         ≡⟨ cong (_+ bs1) (sym (+0 0#)) ⟩
                           (0# + 0#) + bs1
                    end≡

minus 1b 0# 0#      =  (0# , minuend< (0<bs1 []) refl) 
minus 0b 0# (bs 1#) =  (0# , minuend< 0<0+bs1 refl)
                       where
                       bs1     = bs 1#
                       0<0+bs1 = begin 0#         <[ 0<bs1 bs ]
                                       bs1        ≡[ sym (0+ bs1) ]
                                       0# + bs1
                                 ∎

minus 1b 0# (bs 1#) =  (0# , minuend< 0<1+bs1 refl) where
                                                    0<1+bs1 = 0<1+x (bs 1#) 

minus 1b ([] 1#) 0# =  (0# , minuend≡ 1≡<1+0>+0 (refl {x = 0#}))
                where
                1≡<1+0>+0 : 1' ≡ (1' + 0#) + 0#
                1≡<1+0>+0 = begin≡ 1'               ≡⟨ sym (+0 1') ⟩
                                   1' + 0#          ≡⟨ sym (+0 (1' + 0#)) ⟩
                                   (1' + 0#) + 0#
                            end≡  

minus 0b ([] 1#) ([] 1#)       =  (0# , minuend≡ (sym (0+ 1')) refl)
minus 0b ([] 1#) ((b ∷ bs) 1#) =  (0# , minuend< 1<0+bbs1 refl)
         where
         bbs1   = (b ∷ bs) 1#
         |bs:1| = ln (bs ∷ʳ 1b)

         1<1+|bs:1| = ≤nBegin 2              ≤n[ m≤m+n 2 (ln bs) ]
                              2 +n (ln bs)  ≡≤n[ cong 1+_ $
                                                   sym (length-xs:x 1b bs) ]
                              1+ |bs:1|            
                      ≤nEnd

         1<0+bbs1 :  1' < 0# + bbs1  
         1<0+bbs1 =  begin [] 1#             <[ inj₁ 1<1+|bs:1| ]
                           (b ∷ bs) 1#       ≡[ sym (0+ bbs1) ]
                           0# + (b ∷ bs) 1#  
                     ∎

minus 1b ([] 1#) ([] 1#)       =  (0# , minuend< (x<1+x 1') refl)
minus 1b ([] 1#) ((b ∷ bs) 1#) =  (0# , minuend< 1<1+bbs1 (refl {x = 0#}))
      where
      bbs1     = (b ∷ bs) 1#
      1<1+bbs1 = <-trans {1'} {bbs1} {suc bbs1} (1<bbs1 b bs) (x<1+x bbs1)  

minus 0b ((b ∷ bs) 1#) ([] 1#) =  
                          (pred-bbs1 , minuend> 0+1<bbs1 bbs1≡<0+1>+pred-bbs1)
      where
      bbs1      = (b ∷ bs) 1#
      pred-bbs1 = pred bbs1
      0+1≡1     = 0+ 1'

      0+1<bbs1 :  0# + 1' < bbs1
      0+1<bbs1 =  subst (_< bbs1) (sym (0+ 1')) (1<bbs1 b bs)

      bbs1≡<0+1>+pred-bbs1 :  bbs1 ≡ (0# + 1') + pred-bbs1
      bbs1≡<0+1>+pred-bbs1 =  
           begin≡
             bbs1                    ≡⟨ sym (suc∘pred (b ∷ bs)) ⟩
             suc pred-bbs1           ≡⟨ refl ⟩
             1' + pred-bbs1          ≡⟨ cong (_+ pred-bbs1) (sym (0+ 1')) ⟩
             (0# + 1') + pred-bbs1
           end≡

minus 1b ((b ∷ bs) 1#) 0# =  (d , minuend> 1+0<bbs1 bbs1≡1+0+d)
                             where
                             bbs1       = (b ∷ bs) 1# 
                             d          = pred bbs1
                             bbs1≡1+0+d = sym (suc∘pred (b ∷ bs))
                             1+0<bbs1   = 1<bbs1 b bs

minus 1b ((0b ∷ []) 1#) ([] 1#) =  (0# ,   minuend≡ refl refl)
minus 1b ((1b ∷ []) 1#) ([] 1#) =  (1' , minuend> 2<3  refl)
                                   where
                                   2<3 = x<1+x 2'

minus 1b ((b ∷ b' ∷ bs) 1#) ([] 1#) =  (d , minuend> 2<bb'bs1 bb'bs1≡2+d)
    where
    bb'bs  = b ∷ b' ∷ bs
    bb'bs1 = bb'bs 1#
    d      = pred (pred bb'bs1)

    2<|bb'bs1| :  2 <n ln (bb'bs ∷ʳ 1b) 
    2<|bb'bs1| = 
          ≤nBegin 3                          ≤n[ m≤m+n 3 (ln bs) ] 
                  3 +n (ln bs)              ≡≤n[ sym (length-xs:x 1b bb'bs) ]
                  ln ((b ∷ b' ∷ bs) ∷ʳ 1b) 
          ≤nEnd

    2<bb'bs1      = inj₁ 2<|bb'bs1|
    1<bb'bs1      = inj₁ (m≤m+n 2 (ln (bs ∷ʳ 1b))) 
    0<pred-bb'bs1 = pred-mono-< [] bb'bs1 1<bb'bs1 

    bb'bs1≡2+d :  bb'bs1 ≡ 2' + d
    bb'bs1≡2+d = 
       begin≡
         bb'bs1               ≡⟨ sym (suc∘pred bb'bs) ⟩
         suc (pred bb'bs1)    ≡⟨ cong suc (sym (suc∘pred-for>0 {pred bb'bs1}
                                                               0<pred-bb'bs1)) 
                               ⟩
         suc (suc (pred (pred bb'bs1)))  ≡⟨ sym (+-assoc 1' 1' 
                                                       (pred (pred bb'bs1))) ⟩
         2' + pred (pred bb'bs1)
       end≡


minus c ((b ∷ bs) 1#) ((b' ∷ bs') 1#) =  aux c b b' 
  where
  bs1    = bs 1#;          0bs1  = (0b ∷ bs)  1#
  bs'1   = bs' 1#;         0bs'1 = (0b ∷ bs') 1#
  1bs1   = (1b ∷ bs) 1#;   1bs'1 = (1b ∷ bs') 1#
  bs'1*2 = bs'1 * 2' 

  aux : ∀ c b b' → ∃ (\d → MinusRes c ((b ∷ bs) 1#) ((b' ∷ bs') 1#) d)

  aux ⊥b 
  aux _  ⊥b 
  aux _  _  ⊥b 

  ----------------------------------------------
  aux 0b 0b 0b   with  minus 0b (bs 1#) (bs' 1#)   -- no carry
  ...
      | (_ , minuend< bs1<0+bs'1 _) =  (0# , minuend< 0bs1<0+0bs'1 refl)
        where
        bs1<bs'1 :  bs1 < bs'1
        bs1<bs'1 =  subst (bs1 <_) (0+ bs'1) bs1<0+bs'1

        0bs1<0+0bs'1 :  0bs1 < 0# + 0bs'1                             
        0bs1<0+0bs'1 =
             begin 0bs1         ≡[ *2≗*2bin bs1 ]
                   bs1 * 2'     <[ *bs1-mono-< [ 0b ] {bs1} {bs'1} bs1<bs'1 ]
                   bs'1 * 2'    ≡[ sym (*2≗*2bin bs'1) ]
                   bs'1 *2      ≡[ sym (0+ 0bs'1) ] 
                   0# + 0bs'1 
             ∎

  ... | (_ , minuend≡ bs1≡0+bs'1 _) = (0# , minuend≡ 0bs1≡0+0bs'1 refl)
      where
      0bs1≡0+0bs'1 :  (0b ∷ bs) 1# ≡ 0# + (0b ∷ bs') 1#   
      0bs1≡0+0bs'1 = 
             begin≡ (0b ∷ bs) 1#         ≡⟨ refl ⟩
                    (bs 1#) *2           ≡⟨ cong _*2 bs1≡0+bs'1 ⟩
                    (0# + (bs' 1#)) *2   ≡⟨ cong _*2 (0+ (bs' 1#)) ⟩
                    (bs' 1#) *2          ≡⟨ refl ⟩
                    (0b ∷ bs') 1#        ≡⟨ sym (0+ ((0b ∷ bs') 1#)) ⟩
                    0# + (0b ∷ bs') 1#   
             end≡

  ... | (d , minuend> 0+bs'1<bs1 bs1≡0+bs'1+d) =  
                                (d*2 , minuend> 0+0bs'1<0bs1 0bs1≡0+0bs'1+d*2)
        where
        d*2        = d *2
        bs'1<bs1   = subst (_< bs1) (0+ bs'1) 0+bs'1<bs1  
        bs1≡bs'1+d = trans bs1≡0+bs'1+d (cong (_+ d) (0+ bs'1))

        0+0bs'1<0bs1 :  0# + 0bs'1 < 0bs1
        0+0bs'1<0bs1 =
                begin 
                  0# + 0bs'1   ≡[ 0+ 0bs'1 ]
                  bs'1 *2      ≡[ *2≗*2bin bs'1 ]
                  bs'1 * 2'    <[ *bs1-mono-< [ 0b ] {bs'1} {bs1} bs'1<bs1 ] 
                  bs1 * 2'     ≡[ sym (*2≗*2bin bs1) ]
                  bs1 *2       ≡[ refl ]
                  0bs1
                ∎  

        0bs1≡0+0bs'1+d*2 :  0bs1 ≡ (0# + 0bs'1) + d*2
        0bs1≡0+0bs'1+d*2 =  
               begin≡ (0b ∷ bs) 1#         ≡⟨ refl ⟩
                      bs1 *2               ≡⟨ cong _*2 bs1≡bs'1+d ⟩
                      (bs'1 + d) *2        ≡⟨ *2-distrib bs'1 d ⟩
                      bs'1 *2 + d *2       ≡⟨ cong (_+ d*2) (sym (0+ 0bs'1)) ⟩
                      (0# + 0bs'1) + d*2
               end≡

  ---------------------------------------------
  aux 0b 0b 1b  with  minus 1b (bs 1#) (bs' 1#)   -- process carry
  ...
      | (_ , minuend< bs1<1+bs'1 _) =  (0# , minuend< 0bs1<0+1bs'1 refl)
      where   
      1+bs1≤1+bs'1 = <⇒suc≤ {bs1} {suc bs'1} bs1<1+bs'1

      bs1≤bs'1 = begin bs1               ≡[ sym (pred∘suc bs1) ]
                       pred (suc bs1)    ≤[ pred-mono-≤ 1+bs1≤1+bs'1 ]
                       pred (suc bs'1)   ≡[ pred∘suc bs'1 ]
                       bs'1
                 ∎

      0bs1<0+1bs'1 :  0bs1 < 0# + 1bs'1
      0bs1<0+1bs'1 =  
                   begin 0bs1            ≡[ refl ]
                         bs1 *2          ≤[ *2-mono-≤ bs1≤bs'1 ]
                         bs'1 *2         <[ x<1+x (bs'1 *2) ] 
                         1' + bs'1 *2    ≡[ suc-even1 bs' ]
                         1bs'1           ≡[ sym (0+  1bs'1) ]
                         0# + 1bs'1
                   ∎

  ... | (_ , minuend≡ bs1≡1+bs'1 _) =  
                                (1' , minuend> 0+1bs'1<0bs1 0bs1≡0+1bs'1+1) 
      where
      0bs1≡0+1bs'1+1 :  0bs1 ≡ (0# + 1bs'1) + 1'    
      0bs1≡0+1bs'1+1 =  
        begin≡
          bs1 *2                  ≡⟨ cong _*2 bs1≡1+bs'1 ⟩
          (1' + bs'1) *2          ≡⟨ *2≗*2bin _ ⟩
          (1' + bs'1) * 2'        ≡⟨ rDistrib 2' 1' bs'1 ⟩
          1' * 2' + bs'1 * 2'     ≡⟨ refl ⟩
          (1' + 1') + bs'1 * 2'   ≡⟨ +-assoc 1' 1' (bs'1 * 2') ⟩
          1' + (1' + bs'1 * 2')   ≡⟨ cong ((1' +_) ∘ (1' +_))
                                                     (sym (*2≗*2bin bs'1))
                                   ⟩
          1' + (1' + bs'1 *2)     ≡⟨ +-comm 1' (1' + bs'1 *2) ⟩
          (1' + bs'1 *2) + 1'     ≡⟨ refl ⟩ 
          (0# + 1bs'1) + 1'    
        end≡

      le =  x<x+1 (0# + 1bs'1)

      0+1bs'1<0bs1 :  0# + 1bs'1 < 0bs1
      0+1bs'1<0bs1 =  subst ((0# + 1bs'1) <_) (sym 0bs1≡0+1bs'1+1) le


  ... | (d , minuend> 1+bs'1<bs1 bs1≡1+bs'1+d) =  
                            (1+d*2 , minuend> 0+1bs'1<0bs1 0bs1≡0+1bs'1+1+d*2) 
      where
      d*2   = d * 2'
      1+d*2 = suc d*2

      0bs1≡0+1bs'1+1+d*2 :  0bs1 ≡ (0# + 1bs'1) + 1+d*2  
      0bs1≡0+1bs'1+1+d*2 =  
        begin≡
          0bs1                         ≡⟨ refl ⟩
          bs1 *2                       ≡⟨ *2≗*2bin bs1 ⟩
          bs1 * 2'                     ≡⟨ cong (_* 2') bs1≡1+bs'1+d ⟩
          ((suc bs'1) + d) * 2'        ≡⟨ rDistrib 2' (suc bs'1) d ⟩
          (1' + bs'1) * 2'  +  d*2     ≡⟨ cong (_+ d*2) (rDistrib 2' 1' bs'1) 
                                        ⟩
          ((1' + 1') + bs'1*2) + d*2   ≡⟨ cong (_+ d*2) (+-assoc 1' 1' bs'1*2) 
                                        ⟩
          (1' + (suc bs'1*2)) + d*2    ≡⟨ cong (_+ d*2) 
                                               (+-comm 1' (suc bs'1*2))
                                        ⟩
          ((suc bs'1*2) + 1') + d*2    ≡⟨ +-assoc (suc bs'1*2) 1' d*2 ⟩
          (suc bs'1*2) + 1+d*2         ≡⟨ cong ((_+ 1+d*2) ∘ suc)
                                               (sym (*2≗*2bin bs'1))
                                        ⟩
          (suc (bs'1 *2)) + 1+d*2      ≡⟨ cong (_+ 1+d*2) (suc-even1 bs') ⟩
          1bs'1 + 1+d*2                ≡⟨ cong (_+ 1+d*2) (sym (0+ 1bs'1)) ⟩
          (0# + 1bs'1) + 1+d*2  
        end≡

      0+1bs'1<0bs1 :  0# + 1bs'1 < 0bs1
      0+1bs'1<0bs1 =  
        begin 
          0# + 1bs'1                  <[ x<1+x (0# + 1bs'1) ]
          suc (0# + 1bs'1)            ≡[ +-comm 1' (0# + 1bs'1) ]
          (0# + 1bs'1) + 1'           ≡[ sym (+0 ((0# + 1bs'1) + 1')) ]
          ((0# + 1bs'1) + 1') + 0#    ≤[ +-mono-≤ (≤-refl {(0# + 1bs'1) + 1'})
                                                                    (0≤ d*2) ]
          ((0# + 1bs'1) + 1') + d*2   ≡[ +-assoc (0# + 1bs'1) 1' d*2 ]
          (0# + 1bs'1) + 1+d*2        ≡[ sym 0bs1≡0+1bs'1+1+d*2 ]
          0bs1
        ∎

  ------------
  aux 0b 1b 0b  with  minus 0b (bs 1#) (bs' 1#)   -- 1bs1 - 0bs'1,  no carry
  ...
      | (_ , minuend< bs1<0+bs'1 _) =  (0# , minuend< 1bs1<0+0bs'1 refl)
      where   
      1+bs1≤0+bs'1 :  1' + bs1 ≤ 0# + bs'1 
      1+bs1≤0+bs'1 =  <⇒suc≤ {bs1} {0# + bs'1} bs1<0+bs'1

      1bs1<0+0bs'1 :  1bs1 < 0# + 0bs'1
      1bs1<0+0bs'1 =  
           begin
             1bs1                    ≡[ sym (suc-even1 bs) ] 
             suc (bs1 *2)            ≡[ cong suc (*2≗*2bin bs1) ] 
             suc (bs1 * 2')          <[ x<1+x (suc (bs1 * 2')) ]
             1' + (1' + bs1 * 2')    ≡[ sym (+-assoc 1' 1' (bs1 * 2')) ] 
             2' + bs1 * 2'           ≡[ refl ] 
             1' * 2' + bs1 * 2'      ≡[ sym (rDistrib 2' 1' bs1) ]
             (suc bs1) * 2'          ≤[ *-mono-≤ 1+bs1≤0+bs'1 ≤-refl ]
             (0# + bs'1) * 2'        ≡[ cong (_* 2') (0+ bs'1) ] 
             bs'1 * 2'               ≡[ sym (*2≗*2bin bs'1) ] 
             0bs'1                   ≡[ sym (0+ 0bs'1) ] 
             0# + 0bs'1
           ∎

  ... | (_ , minuend≡ bs1≡0+bs'1 _) =  
                                 (1' , minuend> 0+0bs'1<1bs1 1bs1≡0+0bs'1+1)
      where
      0+0bs'1  = 0# + 0bs'1
      bs1≡bs'1 = trans bs1≡0+bs'1 (0+ bs'1)

      1bs1≡0+0bs'1+1 :  1bs1 ≡ 0+0bs'1 + 1'
      1bs1≡0+0bs'1+1 = 
            begin≡ 1bs1                 ≡⟨ sym (suc-even1 bs) ⟩
                   suc (bs1 *2)         ≡⟨ cong (suc ∘ _*2) bs1≡bs'1 ⟩
                   suc (bs'1 *2)        ≡⟨ refl ⟩
                   suc 0bs'1            ≡⟨ +-comm 1' 0bs'1 ⟩
                   0bs'1 + 1'           ≡⟨ cong (_+ 1') (sym (0+ 0bs'1)) ⟩
                   (0# + 0bs'1) + 1'
            end≡

      0+0bs'1<1bs1 :  0+0bs'1 < 1bs1
      0+0bs'1<1bs1 = 
          begin 0+0bs'1         ≡[ sym (+0 0+0bs'1) ]
                0+0bs'1 + 0#    <[ +-mono-≤-< {0+0bs'1} {0+0bs'1} {0#} {1'} 
                                              (≤-refl {0+0bs'1}) (0<bs1 []) ]
                0+0bs'1 + 1'    ≡[ sym 1bs1≡0+0bs'1+1 ] 
                1bs1   
          ∎

  ... | (d , minuend> 0+bs'1<bs1 bs1≡0+bs'1+d) =  
                            (1+d*2 , minuend> 0+0bs'1<1bs1 1bs1≡0+0bs'1+1+d*2)
      where
      d*2 = d * 2';   1+d*2 = suc d*2;   0+0bs'1 = 0# + 0bs'1

      1bs1≡0+0bs'1+1+d*2 :  1bs1 ≡ 0+0bs'1 + 1+d*2   
      1bs1≡0+0bs'1+1+d*2 =  
        begin≡
          1bs1                        ≡⟨ sym (suc-even1 bs) ⟩
          suc (bs1 *2)                ≡⟨ cong (suc ∘ _*2) bs1≡0+bs'1+d ⟩
          suc (((0# + bs'1) + d) *2)  ≡⟨ cong (\x → suc ((x + d) *2))
                                                                 (0+ bs'1) ⟩
          suc ((bs'1 + d) *2)         ≡⟨ cong suc (*2≗*2bin (bs'1 + d)) ⟩
          suc ((bs'1 + d) * 2')       ≡⟨ cong suc (rDistrib 2' bs'1 d) ⟩
          suc (bs'1 * 2' + d*2)       ≡⟨ cong (suc ∘ (_+ d*2)) 
                                              (sym (*2≗*2bin bs'1)) ⟩
          1' + (0bs'1 + d*2)          ≡⟨ sym (+-assoc 1' 0bs'1 d*2) ⟩
          (1' + 0bs'1) + d*2          ≡⟨ cong (_+ d*2) (+-comm 1' 0bs'1) ⟩
          (0bs'1 + 1') + d*2          ≡⟨ +-assoc 0bs'1 1' d*2 ⟩
          0bs'1 + 1+d*2               ≡⟨ cong (_+ 1+d*2) (sym (0+ 0bs'1)) ⟩
          (0# + 0bs'1) + 1+d*2   
        end≡

      0+0bs'1<1bs1 :  0+0bs'1 < 1bs1 
      0+0bs'1<1bs1 = 
         begin 0+0bs'1                ≡[ sym (+0 0+0bs'1) ]
               0+0bs'1 + 0#           <[ +-mono-≤-< {0+0bs'1} {_} {0#} {1'}
                                                (≤-refl {0+0bs'1}) (0<bs1 [])
                                       ]
               0+0bs'1 + 1'           ≤[ x≤x+y (0+0bs'1 + 1') d*2 ]
               (0+0bs'1 + 1') + d*2   ≡[ +-assoc 0+0bs'1 1' d*2 ]
               0+0bs'1 + 1+d*2        ≡[ sym 1bs1≡0+0bs'1+1+d*2 ]
               1bs1 
         ∎

  ------------
  aux 0b 1b 1b  with  minus 0b (bs 1#) (bs' 1#)  -- 1bs1 - 1bs'1,  no carry
  ...
      | (_ , minuend< bs1<0+bs'1 _) =  (0# , minuend< 1bs1<0+1bs'1 refl)
      where 
      bs1<bs'1 =  subst (bs1 <_) (0+ bs'1) bs1<0+bs'1

      1bs1<0+1bs'1 :  1bs1 < 0# + 1bs'1 
      1bs1<0+1bs'1 = 
          begin 1bs1            ≡[ sym (suc-even1 bs) ]
                suc (bs1 *2)    <[ suc-mono-< {bs1 *2} {bs'1 *2}
                                           (*2-mono-< {bs1} {bs'1} bs1<bs'1) ]
                suc (bs'1 *2)   ≡[ suc-even1 bs' ]
                1bs'1           ≡[ sym (0+ 1bs'1) ]
                0# + 1bs'1 
          ∎

  ... | (_ , minuend≡ bs1≡0+bs'1 _) =  (0# , minuend≡ 1bs1≡0+1bs'1 refl)
      where
      1bs1≡0+1bs'1 :  1bs1 ≡ 0# + 1bs'1
      1bs1≡0+1bs'1 =  
             begin≡ 1bs1                  ≡⟨ sym (suc-even1 bs) ⟩
                    suc (bs1 *2)          ≡⟨ cong (suc ∘ _*2) bs1≡0+bs'1 ⟩
                    suc ((0# + bs'1) *2)  ≡⟨ cong (suc ∘ _*2) (0+ bs'1) ⟩
                    suc (bs'1 *2)         ≡⟨ suc-even1 bs' ⟩
                    1bs'1                 ≡⟨ sym (0+ 1bs'1) ⟩
                    0# + 1bs'1
             end≡

  ... | (d , minuend> 0+bs'1<bs1 bs1≡0+bs'1+d) =  
                                (d*2 , minuend> 0+1bs'1<1bs1 1bs1≡0+1bs'1+d*2)
      where
      d*2      = d * 2'
      bs'1<bs1 = subst (_< bs1) (0+ bs'1) 0+bs'1<bs1

      1bs1≡0+1bs'1+d*2 :  1bs1 ≡ (0# + 1bs'1) + d*2
      1bs1≡0+1bs'1+d*2 = 
         begin≡ 
           1bs1                        ≡⟨ sym (suc-even1 bs) ⟩
           suc (bs1 *2)                ≡⟨ cong (suc ∘ _*2) bs1≡0+bs'1+d ⟩
           suc (((0# + bs'1) + d) *2)  ≡⟨ cong (\x → suc ((x + d) *2)) 
                                                                  (0+ bs'1) ⟩
           suc ((bs'1 + d) *2)         ≡⟨ cong suc (*2≗*2bin (bs'1 + d)) ⟩
           suc ((bs'1 + d) * 2')       ≡⟨ cong suc (rDistrib 2' bs'1 d) ⟩
           suc (bs'1 * 2' + d*2)       ≡⟨ sym (+-assoc 1' (bs'1 * 2') d*2) ⟩
           suc (bs'1 * 2') + d*2       ≡⟨ cong ((_+ d*2) ∘ suc) 
                                                       (sym (*2≗*2bin bs'1)) ⟩
           suc (bs'1 *2) + d*2         ≡⟨ cong (_+ d*2) (suc-even1 bs') ⟩
           1bs'1 + d*2                 ≡⟨ cong (_+ d*2) (sym (0+ 1bs'1)) ⟩
           (0# + 1bs'1) + d*2
         end≡

      0+1bs'1<1bs1 :  0# + 1bs'1 < 1bs1 
      0+1bs'1<1bs1 = 
              begin 0# + 1bs'1      ≡[ 0+ _ ]
                    1bs'1           ≡[ sym (suc-even1 bs') ]
                    suc (bs'1 *2)   <[ suc-mono-< {bs'1 *2} {bs1 *2}
                                           (*2-mono-< {bs'1} {bs1} bs'1<bs1) ]
                    suc (bs1 *2)    ≡[ suc-even1 bs ]
                    1bs1 
              ∎

  ------------
  aux 1b 0b 0b  with  minus 1b (bs 1#) (bs' 1#)  -- 0bs1 - 0bs'1  with carry
  ...
      | (_ , minuend< bs1<1+bs'1 _) =  (0# , minuend< 0bs1<1+0bs'1 refl)
      where 
      1+bs1≤1+bs'1 =  <⇒suc≤ {bs1} {1' + bs'1} bs1<1+bs'1 

      0bs1<1+0bs'1 :  0bs1 < 1' + 0bs'1 
      0bs1<1+0bs'1 =  
        suc≤⇒< {0bs1} {suc 0bs'1} 
        (begin 
          1' + 0bs1                   ≡[ refl ]
          1' + bs1 *2                 ≡[ sym (pred∘suc (1' + bs1 *2)) ]
          pred (suc (1' + bs1 *2))    ≡[ refl ]
          pred (1' + (1' + bs1 *2))   ≡[ cong pred $ sym   
                                                    (+-assoc 1' 1' (bs1 *2)) ]
          pred (2' + bs1 *2)          ≡[ cong pred (sym (*2-distrib 1' bs1)) ] 
          pred ((1' + bs1) *2)        ≤[ pred-mono-≤ (*2-mono-≤ 1+bs1≤1+bs'1) 
                                       ]
          pred ((1' + bs'1) *2)       ≡[ cong pred (*2-distrib 1' bs'1) ]
          pred ((suc 1') + bs'1 *2)   ≡[ cong pred (+-assoc 1' 1' (bs'1 *2)) ]
          pred (suc (1' + bs'1 *2))   ≡[ pred∘suc (1' + bs'1 *2) ] 
          1' + bs'1 *2                ≡[ refl ]
          1' + 0bs'1                    
         ∎)

  ... | (_ , minuend≡ bs1≡1+bs'1 _) =  
                                 (1' , minuend> 1+0bs'1<0bs1 0bs1≡1+0bs'1+1)
      where 
      0bs1≡1+0bs'1+1 :  0bs1 ≡ (suc 0bs'1) + 1'
      0bs1≡1+0bs'1+1 =
             begin≡ 0bs1                   ≡⟨ refl ⟩
                    bs1 *2                 ≡⟨ cong _*2 bs1≡1+bs'1 ⟩
                    (1' + bs'1) *2         ≡⟨ *2-distrib 1' bs'1 ⟩
                    2' + bs'1 *2           ≡⟨ +-assoc 1' 1' (bs'1 *2) ⟩
                    1' + (suc (bs'1 *2))   ≡⟨ +-comm 1' (suc (bs'1 *2)) ⟩
                    (suc 0bs'1) + 1'
             end≡  

      1+0bs'1<0bs1 :  suc 0bs'1 < 0bs1 
      1+0bs'1<0bs1 = 
                   begin suc 0bs'1           <[ x<1+x (suc 0bs'1) ]
                         1' + (suc 0bs'1)    ≡[ +-comm 1' (suc 0bs'1) ]
                         (suc 0bs'1) + 1'    ≡[ sym 0bs1≡1+0bs'1+1 ]
                         0bs1 
                   ∎

  ... | (d , minuend> 1+bs'1<bs1 bs1≡1+bs'1+d) = 
                            (1+d*2 , minuend> 1+0bs'1<0bs1 0bs1≡1+0bs'1+1+d*2)
      where
      d*2   = d *2
      1+d*2 = suc d*2

      0bs1≡1+0bs'1+1+d*2 :  0bs1 ≡ (suc 0bs'1) + 1+d*2
      0bs1≡1+0bs'1+1+d*2 = 
        begin≡
          0bs1                           ≡⟨ refl ⟩
          bs1 *2                         ≡⟨ cong _*2 bs1≡1+bs'1+d ⟩
          ((suc bs'1) + d) *2            ≡⟨ *2-distrib (suc bs'1) d ⟩
          (suc bs'1) *2 + d*2            ≡⟨ cong (_+ d*2) (*2-distrib 1' bs'1)
                                          ⟩
          (2' + bs'1 *2) + d*2           ≡⟨ cong (_+ d*2) 
                                                 (+-assoc 1' 1' (bs'1 *2))
                                          ⟩
          (1' + (suc (bs'1 *2))) + d*2   ≡⟨ cong (_+ d*2) 
                                                 (+-comm 1' (suc (bs'1 *2)))
                                            ⟩
          (suc (bs'1 *2) + 1') + d*2     ≡⟨ +-assoc (suc (bs'1 *2)) 1' d*2 ⟩
          suc (bs'1 *2) + 1+d*2          ≡⟨ refl ⟩
          (suc 0bs'1) + 1+d*2
        end≡

      1+0bs'1<0bs1 :  suc 0bs'1 < 0bs1  
      1+0bs'1<0bs1 = 
           begin
             suc 0bs'1                   <[ x<1+x (suc 0bs'1) ]
             suc (suc 0bs'1)             ≡[ +-comm 1' (suc 0bs'1) ]
             (suc 0bs'1) + 1'            ≤[ x≤x+y ((suc 0bs'1) + 1') d*2 ]
             ((suc 0bs'1) + 1') + d*2    ≡[ +-assoc (suc 0bs'1) 1' d*2 ]
             (suc 0bs'1) + 1+d*2         ≡[ sym 0bs1≡1+0bs'1+1+d*2 ]
             0bs1 
           ∎

  ------------
  aux 1b 0b 1b  with  minus 1b (bs 1#) (bs' 1#)  -- 0bs1 - 1bs'1  with carry
  ...
      | (_ , minuend< bs1<1+bs'1 _) =  (0# , minuend< 0bs1<1+1bs'1 refl)
      where 
      1+bs1≤1+bs'1 = <⇒suc≤ {bs1} {suc bs'1} bs1<1+bs'1

      0bs1<1+1bs'1 :  0bs1 < suc 1bs'1
      0bs1<1+1bs'1 = 
        begin 0bs1                  ≡[ refl ]
              bs1 *2                <[ *2-mono-< {bs1} {suc bs1} (x<1+x bs1) ]
              (suc bs1) *2          ≤[ *2-mono-≤ 1+bs1≤1+bs'1 ]
              (suc bs'1) *2         ≡[ *2-distrib 1' bs'1 ]
              2' + (bs'1 *2)        ≡[ +-assoc 1' 1' (bs'1 *2) ]
              suc (suc (bs'1 *2))   ≡[ cong suc (suc-even1 bs') ]
              suc 1bs'1
        ∎

  ... | (_ , minuend≡ bs1≡1+bs'1 _) =  (0# , minuend≡ 0bs1≡1+1bs'1 refl)
      where
      0bs1≡1+1bs'1 :  0bs1 ≡ suc 1bs'1 
      0bs1≡1+1bs'1 =
                 begin≡ 0bs1                 ≡⟨ refl ⟩
                        bs1 *2               ≡⟨ cong _*2 bs1≡1+bs'1 ⟩
                        (suc bs'1) *2        ≡⟨ *2-distrib 1' bs'1 ⟩
                        2' + bs'1 *2         ≡⟨ +-assoc 1' 1' (bs'1 *2) ⟩
                        suc (suc (bs'1 *2))  ≡⟨ cong suc (suc-even1 bs') ⟩
                        suc 1bs'1 
                 end≡

  ... | (d , minuend> 1+bs'1<bs1 bs1≡1+bs'1+d) =
                                (d*2 , minuend> 1+1bs'1<0bs1 0bs1≡1+1bs'1+d*2)
      where
      d*2 = d *2

      0bs1≡1+1bs'1+d*2 :  0bs1 ≡ (suc 1bs'1) + d*2
      0bs1≡1+1bs'1+d*2 = 
        begin≡
          0bs1                          ≡⟨ refl ⟩
          bs1 *2                        ≡⟨ cong _*2 bs1≡1+bs'1+d ⟩
          ((suc bs'1) + d) *2           ≡⟨ *2-distrib (suc bs'1) d ⟩
          (suc bs'1) *2 + d*2           ≡⟨ cong (_+ d*2) 
                                                (*2-distrib 1' bs'1) ⟩
          (2' + bs'1 *2) + d*2          ≡⟨ cong (_+ d*2) 
                                                (+-assoc 1' 1' (bs'1 *2))
                                         ⟩
          (suc (suc (bs'1 *2))) + d*2   ≡⟨ cong ((_+ d*2) ∘ suc)
                                                (suc-even1 bs') ⟩
          (suc 1bs'1) + d*2          
        end≡

      bs'1<bs1     =  <-trans {bs'1} {suc bs'1} {bs1} (x<1+x bs'1) 1+bs'1<bs1
      1+1+bs'1≤bs1 =  <⇒suc≤ {suc bs'1} {bs1} 1+bs'1<bs1

      1+1bs'1<0bs1 :  suc 1bs'1 < 0bs1 
      1+1bs'1<0bs1 =
        begin
          suc 1bs'1                ≡[ cong suc (sym (suc-even1 bs')) ]
          suc (suc (bs'1 *2))      ≡[ sym (+-assoc 1' 1' (bs'1 *2)) ]
          2' + bs'1 *2             ≡[ cong (2' +_) (*2≗+ bs'1) ]
          2' + (bs'1 + bs'1)       ≡[ sym (+-assoc 2' bs'1 bs'1) ] 
          (2' + bs'1) + bs'1       ≡[ cong (_+ bs'1) (+-assoc 1' 1' bs'1) 
                                    ]
          (suc (suc bs'1)) + bs'1  ≤[ +-mono-≤ 1+1+bs'1≤bs1 (≤-refl {bs'1}) ]
          bs1 + bs'1               <[ +-mono-≤-< {bs1} {bs1} {bs'1} {bs1}
                                                     (≤-refl {bs1}) bs'1<bs1 ]
          bs1 + bs1                ≡[ sym (*2≗+ bs1) ]
          bs1 *2                   ≡[ refl ]
          0bs1 
        ∎

  ------------
  aux 1b 1b 0b  with  minus 0b (bs 1#) (bs' 1#)  -- 1bs1 - 0bs'1, no subcarry
  ...
      | (_ , minuend< bs1<0+bs'1 _) =  (0# , minuend< 1bs1<1+0bs'1 refl)
      where 
      bs1<bs'1 = subst (bs1 <_) (0+ bs'1) bs1<0+bs'1

      1bs1<1+0bs'1 :  1bs1 < suc 0bs'1
      1bs1<1+0bs'1 = 
        begin 1bs1            ≡[ sym (suc-even1 bs) ]
              suc (bs1 *2)    <[ suc-mono-< {bs1 *2} {bs'1 *2} 
                                          (*2-mono-< {bs1} {bs'1} bs1<bs'1) ]
              suc (bs'1 *2)   ≡[ refl ]
              suc 0bs'1
        ∎

  ... | (_ , minuend≡ bs1≡0+bs'1 _) =  (0# , minuend≡ 1bs1≡1+0bs'1 refl)
      where
      1bs1≡1+0bs'1 :  1bs1 ≡ suc 0bs'1 
      1bs1≡1+0bs'1 = 
             begin≡ 1bs1                  ≡⟨ sym (suc-even1 bs) ⟩
                    suc (bs1 *2)          ≡⟨ cong (suc ∘ _*2) bs1≡0+bs'1 ⟩
                    suc ((0# + bs'1) *2)  ≡⟨ cong (suc ∘ _*2) (0+ bs'1) ⟩
                    suc (bs'1 *2)         ≡⟨ refl ⟩
                    suc 0bs'1 
             end≡
 
  ... | (d , minuend> 0+bs'1<bs1 bs1≡0+bs'1+d) = 
                             (d*2 , minuend> 1+0bs'1<1bs1 1bs1≡1+0bs'1+d*2)
      where
      d*2        =  d *2
      bs1≡bs'1+d =  trans bs1≡0+bs'1+d (cong (_+ d) (0+ bs'1))
      bs'1<bs1   =  subst (_< bs1) (0+ bs'1) 0+bs'1<bs1

      1bs1≡1+0bs'1+d*2 :  1bs1 ≡ (suc 0bs'1) + d*2
      1bs1≡1+0bs'1+d*2 = 
          begin≡ 1bs1                    ≡⟨ sym (suc-even1 bs) ⟩
                 suc (bs1 *2)            ≡⟨ cong (suc ∘ _*2) bs1≡bs'1+d ⟩
                 suc ((bs'1 + d) *2)     ≡⟨ cong suc (*2-distrib bs'1 d) ⟩
                 suc (bs'1 *2 + d*2)     ≡⟨ sym (+-assoc 1' (bs'1 *2) d*2) ⟩
                 (suc (bs'1 *2)) + d*2   ≡⟨ refl ⟩
                 (suc 0bs'1) + d*2
          end≡

      1+0bs'1<1bs1 :  suc 0bs'1 < 1bs1
      1+0bs'1<1bs1 = 
         begin suc 0bs'1      ≡[ refl ]
               suc (bs'1 *2)  <[ suc-mono-< {bs'1 *2} {bs1 *2} 
                                          (*2-mono-< {bs'1} {bs1} bs'1<bs1) ]
               suc (bs1 *2)   ≡[ suc-even1 bs ]
               1bs1
         ∎

  ------------
  aux 1b 1b 1b  with  minus 1b (bs 1#) (bs' 1#)  -- 1bs1 - 1bs'1, subcarry
  ...
      | (_ , minuend< bs1<1+bs'1 _) =  (0# , minuend< 1bs1<1+1bs'1 refl)
      where 
      1+bs1≤1+bs'1 =  <⇒suc≤ {bs1} {suc bs'1} bs1<1+bs'1

      1bs1<1+1bs'1 :  1bs1 < suc 1bs'1
      1bs1<1+1bs'1 =
        begin 1bs1                 ≡[ sym (suc-even1 bs) ]
              suc (bs1 *2)         <[ x<1+x (suc (bs1 *2)) ] 
              suc (suc (bs1 *2))   ≡[ sym (+-assoc 1' 1' (bs1 *2)) ] 
              2' + bs1 *2          ≡[ cong (2' +_) (*2≗*2bin bs1) ]
              2' + bs1 * 2'        ≤[ x<y⇒a+x*a≤y*a {bs1} {suc bs'1} 2'  
                                                               bs1<1+bs'1 ]  
              (suc bs'1) * 2'      ≡[ sym (*2≗*2bin (suc bs'1)) ]
              (suc bs'1) *2        ≡[ *2-distrib 1' bs'1 ]
              2' + bs'1 *2         ≡[ +-assoc 1' 1' (bs'1 *2) ]
              suc (1' + bs'1 *2)   ≡[ cong suc (suc-even1 bs') ]
              suc 1bs'1
        ∎

  ... | (_ , minuend≡ bs1≡1+bs'1 _) =  
                                 (1' , minuend> 1+1bs'1<1bs1 1bs1≡1+1bs'1+1)
      where
      1bs1≡1+1bs'1+1 :  1bs1 ≡ (suc 1bs'1) + 1'
      1bs1≡1+1bs'1+1 = 
        begin≡
          1bs1                       ≡⟨ sym (suc-even1 bs) ⟩
          suc (bs1 *2)               ≡⟨ cong (suc ∘ _*2) bs1≡1+bs'1 ⟩
          suc ((suc bs'1) *2)        ≡⟨ cong suc (*2-distrib 1' bs'1) ⟩
          suc (2' + bs'1 *2)         ≡⟨ cong suc (+-assoc 1' 1' (bs'1 *2)) ⟩
          suc (suc (suc (bs'1 *2)))  ≡⟨ cong (suc ∘ suc) (suc-even1 bs') ⟩
          suc (suc 1bs'1)            ≡⟨ +-comm 1' (suc 1bs'1) ⟩
          (suc 1bs'1) + 1'
        end≡

      1+1bs'1<1bs1 :  suc 1bs'1 < 1bs1 
      1+1bs'1<1bs1 = 
                   begin suc 1bs'1          <[ x<1+x (suc 1bs'1) ]
                         suc (suc 1bs'1)    ≡[ +-comm 1' (suc 1bs'1) ]
                         (suc 1bs'1) + 1'   ≡[ sym 1bs1≡1+1bs'1+1 ]
                         1bs1 
                   ∎

  ... | (d , minuend> 1+bs'1<bs1 bs1≡1+bs'1+d) = 
                            (1+d*2 , minuend> 1+1bs'1<1bs1 1bs1≡1+1bs'1+1+d*2)
      where
      d*2   = d *2
      1+d*2 = suc d*2

      1bs1≡1+1bs'1+1+d*2 :  1bs1 ≡ (suc 1bs'1) + 1+d*2  
      1bs1≡1+1bs'1+1+d*2 =  
        begin≡
          1bs1                           ≡⟨ sym (suc-even1 bs) ⟩
          suc (bs1 *2)                   ≡⟨ cong (suc ∘ _*2) bs1≡1+bs'1+d ⟩
          suc (((suc bs'1) + d) *2)      ≡⟨ cong suc (*2-distrib (suc bs'1) d)
                                          ⟩
          suc ((suc bs'1) *2 + d*2)      ≡⟨ cong (suc ∘ (_+ d*2)) 
                                                       (*2-distrib 1' bs'1) ⟩
          suc ((2' + bs'1 *2) + d*2)     ≡⟨ sym $ +-assoc 1' (2' + bs'1 *2) 
                                                                         d*2 ⟩
          suc (2' + bs'1 *2) + d*2       ≡⟨ cong (_+ d*2)
                                                (+-comm 1' (2' + bs'1 *2)) ⟩
          ((2' + bs'1 *2) + 1') + d*2    ≡⟨ +-assoc (2' + bs'1 *2) 1' d*2 ⟩
          (2' + bs'1 *2) + 1+d*2         ≡⟨ cong (_+ 1+d*2)
                                                 (+-assoc 1' 1' (bs'1 *2)) ⟩
          (suc (suc (bs'1 *2))) + 1+d*2  ≡⟨ cong ((_+ 1+d*2) ∘ suc)
                                                             (suc-even1 bs') ⟩
          (suc 1bs'1) + 1+d*2  
        end≡
  
      1+1bs'1<1bs1 :  suc 1bs'1 < 1bs1
      1+1bs'1<1bs1 = 
        begin
          suc 1bs'1             ≡[ sym (+0 (suc 1bs'1)) ]
          (suc 1bs'1) + 0#      <[ +-mono-≤-< {suc 1bs'1} {suc 1bs'1} 
                                             {0#} {1+d*2} ≤-refl (0<1+x d*2) ]
          (suc 1bs'1) + 1+d*2   ≡[ sym 1bs1≡1+1bs'1+1+d*2 ]
          1bs1
        ∎


------------------------------------------------------------------------------
infixl 6 _∸_

_∸_ :  Op₂ Bin 
x ∸ y =  proj₁ (minus 0b x y) 

x≤y←→x∸y≡0 :  ∀ {x y} → (x ≤ y ←→ x ∸ y ≡ 0#)
x≤y←→x∸y≡0 {x} {y} =
                   (to , from)
  where
  to :  x ≤ y → x ∸ y ≡ 0#
  to x≤y 
     with  minus 0b x y
  ...      | (_ , minuend< _     d≡0) =  d≡0
  ...      | (_ , minuend≡ _     d≡0) =  d≡0
  ...      | (_ , minuend> x>0+y _  ) =  ⊥-elim (≤⇒≯ x≤y x>y)
                                         where
                                         x>y = subst (x >_) (0+ y) x>0+y

  from :  x ∸ y ≡ 0# → x ≤ y
  from x∸y≡0
       with  minus 0b x y
  ...        | (_ , minuend< x<0+y _) =  inj₁ x<y
                                         where
                                         x<y = subst (x <_) (0+ y) x<0+y

  ...        | (_ ,  minuend≡ x≡0+y _      ) =  inj₂ (trans x≡0+y (0+ y))
  ...        | (0# , minuend> 0+y<x x≡0+y+0) =  ⊥-elim (<⇒≢ y<x (sym x≡y))
                         where
                         y<x = subst (_< x) (0+ y) 0+y<x
                         x≡y = begin≡ x               ≡⟨ x≡0+y+0 ⟩
                                      (0# + y) + 0#   ≡⟨ cong (_+ 0#) (0+ y) ⟩
                                      y + 0#          ≡⟨ (+0 y) ⟩
                                      y
                               end≡      

  ...        | (bs 1# , minuend> _ _) =  ⊥-elim (0≢bs1 bs (sym x∸y≡0))


x≤y⇒x∸y≡0 :  ∀ {x y} → x ≤ y → x ∸ y ≡ 0#
x≤y⇒x∸y≡0 {x} {y} x≤y =  
                      proj₁ (x≤y←→x∸y≡0 {x} {y}) x≤y  

x∸y≡0⇒x≤y :  ∀ {x y} → x ∸ y ≡ 0# → x ≤ y
x∸y≡0⇒x≤y {x} {y} x∸y≡0 = 
                        proj₂ (x≤y←→x∸y≡0 {x} {y}) x∸y≡0

open Tri 

x<y⇒0<y∸x :  ∀ {x y} → x < y → 0# < y ∸ x
x<y⇒0<y∸x {x} {y} x<y =
                      case <-cmp (y ∸ x) 0#
                      of \ 
                      { (tri> _ _     gt) → gt
                      ; (tri≈ _ y∸x≡0 _ ) → let y≤x = x∸y≡0⇒x≤y {y} {x} y∸x≡0
                                            in  ⊥-elim (<⇒≱ x<y y≤x) 
                      ; (tri< y∸x<0 _ _ ) → ⊥-elim (≮0 (y ∸ x) y∸x<0)
                      }

x∸x :  ∀ x → x ∸ x ≡ 0#
x∸x x = 
      x≤y⇒x∸y≡0 (≤-refl {x}) 

0∸ :  ∀ x → 0# ∸ x ≡ 0#
0∸ x =  x≤y⇒x∸y≡0 (0≤ x) 

------------------------------------------------------------------------------
[x+y]∸y≡x :  ∀ x y → (x + y) ∸ y ≡ x
[x+y]∸y≡x x y 
            with  minus 0b (x + y) y

... | (_ , minuend< x+y<0+y _  ) =  ⊥-elim (<⇒≱ x+y<0+y 0+y≤x+y)  
                                    where
                                    0+y≤x+y =  +-mono-≤ (0≤ x) (≤-refl {y})

... | (d , minuend≡ x+y≡0+y d≡0) =  trans d≡0 (sym x≡0)
                                    where
                                    x≡0 : x ≡ 0#
                                    x≡0 = +-rCancel y x 0# x+y≡0+y
                                   
... | (d , minuend> 0+y<x+y x+y≡0+y+d) =  sym x≡d
                        where
                        x+y≡d+y = begin≡ x + y         ≡⟨ x+y≡0+y+d ⟩
                                         (0# + y) + d  ≡⟨ cong (_+ d) (0+ y) ⟩
                                         y + d         ≡⟨ +-comm y d ⟩
                                         d + y
                                  end≡

                        x≡d =  +-rCancel y x d x+y≡d+y

------------------
∸0 :  (_∸ 0#) ≗ id
∸0 x = 
     begin≡ x ∸ 0#          ≡⟨ cong (_∸ 0#) (sym (+0 x)) ⟩
            (x + 0#) ∸ 0#   ≡⟨ [x+y]∸y≡x x 0# ⟩
            x
     end≡
                             
----------------------------------------------
x+[y∸x]≡y :  ∀ {x y} → x ≤ y → x + (y ∸ x) ≡ y 
x+[y∸x]≡y {x} {y} x≤y =
                      aux (minus 0b y x)
  where
  aux :  ∃ (\d → MinusRes 0b y x d) → x + (y ∸ x) ≡ y 

  aux (_ , minuend< y<0+x _) =  ⊥-elim (≤⇒≯ x≤y y<x)
                                where 
                                y<x = subst (y <_) (0+ x) y<0+x

  aux (_ , minuend≡ y≡0+x _) =  begin≡ x + (y ∸ x)   ≡⟨ cong (x +_) y∸x≡0 ⟩
                                       x + 0#        ≡⟨ +-comm x 0# ⟩
                                       0# + x        ≡⟨ sym y≡0+x ⟩
                                       y
                                end≡ 
                                where
                                y≡x   =  trans y≡0+x (0+ x)
                                y∸x≡0 =  x≤y⇒x∸y≡0 {y} {x} (inj₂ y≡x)

  aux (d , minuend> 0+x<y y≡0+x+d) =  
                    begin≡ 
                      x + (y ∸ x)        ≡⟨ cong ((x +_) ∘ (_∸ x)) y≡d+x ⟩
                      x + ((d + x) ∸ x)  ≡⟨ cong (x +_) ([x+y]∸y≡x d x) ⟩
                      x + d              ≡⟨ +-comm x d ⟩
                      d + x              ≡⟨ sym y≡d+x ⟩
                      y 
                    end≡
                    where
                    y≡d+x = begin≡ y              ≡⟨ y≡0+x+d ⟩
                                   (0# + x) + d   ≡⟨ cong (_+ d) (0+ x) ⟩
                                   x + d          ≡⟨ +-comm x d ⟩
                                   d + x
                            end≡   

-------------------------
∸1≗pred :  (_∸ 1') ≗ pred  

∸1≗pred 0#      =  refl 
∸1≗pred (bs 1#) =  begin≡ a ∸ 1'           ≡⟨ cong (_∸ 1') (sym 1+pa≡a) ⟩
                          (1' + pa) ∸ 1'   ≡⟨ cong (_∸ 1') (+-comm 1' pa) ⟩
                          (pa + 1') ∸ 1'   ≡⟨ [x+y]∸y≡x pa 1' ⟩ 
                          pa
                   end≡
                   where
                   a = bs 1#;   pa = pred a;  1+pa≡a = suc∘pred bs 

------------------------------------------------------------------------------
toℕ∸homo :  ∀ x y → toℕ (x ∸ y) ≡ (toℕ x) ∸n (toℕ y)
toℕ∸homo x y 
           with <-cmp x y
... | tri< x<y _ _ = 
                   begin≡ toℕ (x ∸ y)   ≡⟨ cong toℕ (x≤y⇒x∸y≡0 {x} {y} x≤y) ⟩
                          toℕ 0#        ≡⟨ refl ⟩
                          0             ≡⟨ sym (NatProp0.≤⇒∸≡0 xN≤yN) ⟩
                          xN ∸n yN
                   end≡ 
                   where
                   xN = toℕ x;   yN = toℕ y;  x≤y = inj₁ x<y
                   xN≤yN = toℕ-mono-≤ x≤y  

... | tri≈ _ x≡y _ = 
             begin≡ toℕ (x ∸ y)   ≡⟨ cong toℕ (x≤y⇒x∸y≡0 {x} {y} x≤y) ⟩
                    toℕ 0#        ≡⟨ refl ⟩
                    0             ≡⟨ sym (NatProp0.≤⇒∸≡0 xN≤yN) ⟩
                    xN ∸n yN
             end≡ 
             where
             xN = toℕ x;  yN = toℕ y;  x≤y = inj₂ x≡y;  xN≤yN = toℕ-mono-≤ x≤y

... | tri> _ _ y<x =
    begin≡ 
      toℕ (x ∸ y)                   ≡⟨ sym (NProp.m+n∸n≡m (toℕ (x ∸ y)) yN) ⟩
      ((toℕ (x ∸ y)) +n yN) ∸n yN   ≡⟨ cong (_∸n yN) eq ⟩
      ((xN ∸n yN) +n yN) ∸n yN      ≡⟨ NProp.m+n∸n≡m (xN ∸n yN) yN ⟩
      xN ∸n yN
    end≡
    where
    xN = toℕ x;  yN = toℕ y;  y≤x = inj₁ y<x

    yN≤xN = toℕ-mono-≤ {y} {x} (inj₁ y<x)
    eq = begin≡ 
           toℕ (x ∸ y) +n yN    ≡⟨ sym (toℕ+homo (x ∸ y) y) ⟩
           toℕ ((x ∸ y) + y)    ≡⟨ cong toℕ (+-comm (x ∸ y) y) ⟩
           toℕ (y + (x ∸ y))    ≡⟨ cong toℕ (x+[y∸x]≡y {y} {x} y≤x) ⟩
           xN                   ≡⟨ sym (NProp.m+n∸m≡n yN≤xN) ⟩
           yN +n (xN ∸n yN)     ≡⟨ +n-comm yN (xN ∸n yN) ⟩
           (xN ∸n yN) +n yN
         end≡

------------------------------------------------------------
fromℕ∸homo :  ∀ m n → fromℕ (m ∸n n) ≡ (fromℕ m) ∸ (fromℕ n)
fromℕ∸homo m n =  
         begin≡ fromℕ (m ∸n n)          ≡⟨ cong fromℕ (cong₂ _∸n_ m≡xN n≡yN) ⟩
                fromℕ (toℕ x ∸n toℕ y)  ≡⟨ cong fromℕ (sym (toℕ∸homo x y)) ⟩
                fromℕ (toℕ (x ∸ y))     ≡⟨ fromℕ∘toℕ (x ∸ y) ⟩
                x ∸ y
         end≡
         where
         x    = fromℕ m;            y    = fromℕ n 
         m≡xN = sym (toℕ∘fromℕ m);  n≡yN = sym (toℕ∘fromℕ n)

------------------------------------------------------------------------------
bs1∸bs'1<bs1 :  ∀ bs bs' → (bs 1#) ∸ (bs' 1#) < bs 1#
bs1∸bs'1<bs1 bs bs' 
                with  <-cmp (bs 1#) (bs' 1#)

... | tri< bs1<bs'1 _ _ =  subst (_< bs1) (sym bs1∸bs'1≡0) (0<bs1 bs) 
                           where
                           bs1        = bs 1#
                           bs'1       = bs' 1#
                           bs1∸bs'1≡0 = x≤y⇒x∸y≡0 {bs1} {bs'1} (inj₁ bs1<bs'1)

... | tri≈ _ bs1≡bs'1 _ =  subst (_< (bs 1#)) (sym bs1∸bs'1≡0) (0<bs1 bs) 
                           where
                           bs1        = bs 1#
                           bs'1       = bs' 1#
                           bs1∸bs'1≡0 = x≤y⇒x∸y≡0 {bs1} {bs'1} (inj₂ bs1≡bs'1)

... | tri> _ _ bs'1<bs1  = 
      begin
        bs1 ∸ bs'1            ≡[ sym (0+ (bs1 ∸ bs'1)) ]           
        0# + (bs1 ∸ bs'1)     <[ +-mono-<-≤ {0#} {bs'1} {bs1 ∸ bs'1} {_} 
                                                        (0<bs1 bs') ≤-refl ]
        bs'1 + (bs1 ∸ bs'1)   ≡[ x+[y∸x]≡y {bs'1} {_} (inj₁ bs'1<bs1) ]  
        bs1        
      ∎
      where  bs1 = bs 1#;  bs'1 = bs' 1# 

------------------------------------------------------------------------------
*-lDistrib-∸ :  FP-Bin._DistributesOverˡ_ _*_ _∸_
*-lDistrib-∸ x y z =  
  begin≡
    x * (y ∸ z)                   ≡⟨ sym (fromℕ∘toℕ (x * (y ∸ z))) ⟩
    fromℕ (toℕ (x * (y ∸ z)))     ≡⟨ cong fromℕ (toℕ*homo x (y ∸ z)) ⟩
    fromℕ (xN *n (toℕ (y ∸ z)))   ≡⟨ cong (fromℕ ∘ (xN *n_)) (toℕ∸homo y z) ⟩
    fromℕ (xN *n (yN ∸n zN))      ≡⟨ cong fromℕ 
                                          (NatProp0.*-lDistrib-∸ xN yN zN) 
                                   ⟩ 
    fromℕ ((xN *n yN) ∸n (xN *n zN))     ≡⟨ fromℕ∸homo (xN *n yN) (xN *n zN) ⟩ 
    fromℕ (xN *n yN) ∸ fromℕ (xN *n zN)
                            ≡⟨ cong₂ _∸_ (fromℕ*homo xN yN) (fromℕ*homo xN zN) 
                             ⟩ 
    (fromℕ xN * fromℕ yN) ∸ (fromℕ xN * fromℕ zN)
                        ≡⟨ cong₂ _∸_ (cong₂ _*_ (fromℕ∘toℕ x) (fromℕ∘toℕ y))
                                     (cong₂ _*_ (fromℕ∘toℕ x) (fromℕ∘toℕ z)) ⟩
    x * y ∸ x * z
  end≡
  where
  xN = toℕ x;  yN = toℕ y;  zN = toℕ z  

------------------------------------------------------------------------------
1+x∸1+y :  ∀ x y → suc x ∸ suc y ≡ x ∸ y
1+x∸1+y x y 
          with <-cmp x y 

... | tri< x<y _ _ =  begin≡ suc x ∸ suc y   ≡⟨ x≤y⇒x∸y≡0 1+x≤1+y ⟩
                             0#              ≡⟨ sym (x≤y⇒x∸y≡0 x≤y) ⟩
                             x ∸ y
                      end≡
                      where   
                      x≤y     = inj₁ x<y
                      1+x≤1+y = suc-mono-≤ {x} {y} x≤y 


... | tri≈ _ x≡y _ =  begin≡ suc x ∸ suc y  ≡⟨ x≤y⇒x∸y≡0 1+x≤1+y ⟩
                             0#             ≡⟨ sym (x≤y⇒x∸y≡0 x≤y) ⟩
                             x ∸ y
                      end≡
                      where   
                      x≤y     = inj₂ x≡y
                      1+x≤1+y = suc-mono-≤ {x} {y} x≤y 

... | tri> _ _ y<x =  +-lCancel y (1+x ∸ 1+y) x∸y eq2
      where
      1+x = suc x;   1+y = suc y;   x∸y = x ∸ y 

      eq0 :  y + x∸y ≡ x
      eq0 =  x+[y∸x]≡y {y} {x} (inj₁ y<x)

      1+y<1+x =  suc-mono-< {y} {x} y<x
      eq1 =  
          begin≡
            suc (y + (1+x ∸ 1+y))   ≡⟨ sym (+-assoc 1' y (1+x ∸ 1+y)) ⟩
            1+y + (1+x ∸ 1+y)       ≡⟨ x+[y∸x]≡y {1+y} {1+x} (inj₁ 1+y<1+x) ⟩
            1+x
          end≡

      eq2 = begin≡ 
              y + (1+x ∸ 1+y)   ≡⟨ +-lCancel 1' (y + (1+x ∸ 1+y)) x eq1 ⟩
              x                 ≡⟨ sym eq0 ⟩
              y + x∸y
            end≡

-----------------------------------------------------------
+-∸-comm :  ∀ {x} y {o} → o ≤ x → (x + y) ∸ o ≡ (x ∸ o) + y
+-∸-comm {x} y {o} o≤x = 
  begin≡ 
    (x + y) ∸ o                   ≡⟨ sym (fromℕ∘toℕ ((x + y) ∸ o)) ⟩   
    fromℕ (toℕ ((x + y) ∸ o))     ≡⟨ cong fromℕ (toℕ∸homo (x + y) o) ⟩   
    fromℕ ((toℕ (x + y)) ∸n oN)   ≡⟨ cong (fromℕ ∘ (_∸n oN)) (toℕ+homo x y) ⟩
    fromℕ ((xN +n yN) ∸n oN)      ≡⟨ cong fromℕ (NProp.+-∸-comm yN oN≤xN) ⟩
    fromℕ ((xN ∸n oN) +n yN)      ≡⟨ fromℕ+homo (xN ∸n oN) yN ⟩
    fromℕ (xN ∸n oN) + fromℕ yN   ≡⟨ cong ((fromℕ (xN ∸n oN)) +_) 
                                                              (fromℕ∘toℕ y) ⟩
    fromℕ (xN ∸n oN) + y          ≡⟨ cong (_+ y) (fromℕ∸homo xN oN) ⟩
    (fromℕ xN ∸ fromℕ oN) + y     ≡⟨ cong (_+ y) 
                                     (cong₂ _∸_ (fromℕ∘toℕ x) (fromℕ∘toℕ o)) ⟩
    (x ∸ o) + y
  end≡
  where
  xN = toℕ x;   yN = toℕ y;   oN = toℕ o;   oN≤xN = toℕ-mono-≤ o≤x 

------------------------------------------------
∸-+-assoc :  ∀ x y o → (x ∸ y) ∸ o ≡ x ∸ (y + o)
∸-+-assoc x y o =
  begin≡ 
    (x ∸ y) ∸ o                   ≡⟨ sym (fromℕ∘toℕ ((x ∸ y) ∸ o)) ⟩   
    fromℕ (toℕ ((x ∸ y) ∸ o))     ≡⟨ cong fromℕ (toℕ∸homo (x ∸ y) o) ⟩   
    fromℕ (toℕ (x ∸ y) ∸n oN)     ≡⟨ cong (fromℕ ∘ (_∸n oN)) (toℕ∸homo x y) ⟩
    fromℕ ((xN ∸n yN) ∸n oN)      ≡⟨ cong fromℕ (NProp.∸-+-assoc xN yN oN) ⟩   
    fromℕ (xN ∸n (yN +n oN))      ≡⟨ fromℕ∸homo xN (yN +n oN) ⟩   
    fromℕ xN ∸ fromℕ (yN +n oN)   ≡⟨ cong ((fromℕ xN) ∸_) (fromℕ+homo yN oN) ⟩
    fromℕ xN ∸ (fromℕ yN + fromℕ oN)
                                  ≡⟨ cong ((fromℕ xN) ∸_) 
                                       (cong₂ _+_ (fromℕ∘toℕ y) (fromℕ∘toℕ o))
                                   ⟩
    fromℕ xN ∸ (y + o)            ≡⟨ cong (_∸ (y + o)) (fromℕ∘toℕ x) ⟩
    x ∸ (y + o)
  end≡
  where
  xN = toℕ x;  yN = toℕ y;  oN = toℕ o

----------------------------------------------------------
+-∸-assoc :  ∀ x {y o} → o ≤ y → (x + y) ∸ o ≡ x + (y ∸ o)
+-∸-assoc x {y} {o} o≤y =
  begin≡
    (x + y) ∸ o                   ≡⟨ sym (fromℕ∘toℕ ((x + y) ∸ o)) ⟩   
    fromℕ (toℕ ((x + y) ∸ o))     ≡⟨ cong fromℕ (toℕ∸homo (x + y) o) ⟩   
    fromℕ (toℕ (x + y) ∸n oN)     ≡⟨ cong (fromℕ ∘ (_∸n oN)) (toℕ+homo x y) ⟩
    fromℕ ((xN +n yN) ∸n oN)      ≡⟨ cong fromℕ (NProp.+-∸-assoc xN oN≤yN) ⟩
    fromℕ (xN +n (yN ∸n oN))      ≡⟨ fromℕ+homo xN (yN ∸n oN) ⟩   
    fromℕ xN + fromℕ (yN ∸n oN)   ≡⟨ cong (_+ (fromℕ (yN ∸n oN)))
                                                            (fromℕ∘toℕ x) ⟩ 
    x + fromℕ (yN ∸n oN)          ≡⟨ cong (x +_) (fromℕ∸homo yN oN) ⟩   
    x + (fromℕ yN ∸ fromℕ oN)     ≡⟨ cong (x +_)
                                      (cong₂ _∸_ (fromℕ∘toℕ y) (fromℕ∘toℕ o))
                                   ⟩ 
    x + (y ∸ o)
  end≡
  where
  xN = toℕ x;  yN = toℕ y;  oN = toℕ o;  oN≤yN = toℕ-mono-≤ o≤y 

------------------------------------------
∸-mono-≤ :  _∸_ Preserves₂ _≤_ ⟶ _≥_ ⟶ _≤_ 
∸-mono-≤ {x} {x'} {y} {y'} x≤x' y'≤y = 
       begin
         x ∸ y                   ≡[ sym (fromℕ∘toℕ (x ∸ y)) ]
         fromℕ (toℕ (x ∸ y))     ≡[ cong fromℕ (toℕ∸homo x y) ]
         fromℕ (xN ∸n yN)        ≤[ fromℕ-mono-≤ (∸n-mono xN≤x'N y'N≤yN) ]
         fromℕ (x'N ∸n y'N)      ≡[ fromℕ∸homo x'N y'N ]
         fromℕ x'N ∸ fromℕ y'N   ≡[ cong₂ _∸_ (fromℕ∘toℕ x') (fromℕ∘toℕ y') ] 
         x' ∸ y'
       ∎
       where  xN = toℕ x;  yN = toℕ y;    x'N = toℕ x';  y'N = toℕ y'
              xN≤x'N = toℕ-mono-≤ x≤x';   y'N≤yN = toℕ-mono-≤ y'≤y

x∸y≤x :  ∀ x y → x ∸ y ≤ x
x∸y≤x x y =
          begin x ∸ y    ≤[ ∸-mono-≤ (≤-refl {x}) (0≤ y) ]  
                x ∸ 0#   ≡[ ∸0 x ]  
                x
          ∎

|x∸y|≤|x| :  ∀ x y → ∣ x ∸ y ∣ ≤n ∣ x ∣
|x∸y|≤|x| x y = 
              ∣_∣-mono-≤ (x∸y≤x x y)


compareN = NProp.<-cmp

------------------------------------------------------------------------------
∸∘2^∘ln≗fromBits :  ∀ bs → (bs 1#) ∸ 2^ (ln bs) ≡ fromBits bs
∸∘2^∘ln≗fromBits bs =
    begin≡
      (bs 1#) ∸ 2^|bs|                     ≡⟨ cong (_∸ 2^|bs|) 
                                                         (partHighest-2^ bs) ⟩
      ((fromBits bs) + 2^|bs|) ∸ 2^|bs|    ≡⟨ [x+y]∸y≡x (fromBits bs) 2^|bs| ⟩
      fromBits bs
    end≡
    where 2^|bs| = 2^ (ln bs)


|bbs1∸2^1+|bs||<|bbs1| :  
            ∀ b bs →  ∣ ((b ∷ bs) 1#) ∸ 2^ (1+ ln bs) ∣  <n  ∣ ((b ∷ bs) 1#) ∣

|bbs1∸2^1+|bs||<|bbs1| b bs =  aux (1b ∈? bbs)
  where
  bbs = b ∷ bs

  aux :  Dec (1b ∈ bbs) → ∣ (bbs 1#) ∸ 2^ (1+ ln bs) ∣ <n ∣ (bbs 1#) ∣
  aux (no 1∉bbs) =  
     ≤nBegin 
       1+ ∣ (bbs 1#) ∸ (2^ (1+ ln bs)) ∣   
                                ≡≤n[ cong (1+_ ∘ ∣_∣) (∸∘2^∘ln≗fromBits bbs) ]
       1+ ∣ fromBits bbs ∣      ≡≤n[ cong (1+_ ∘ ∣_∣) 
                                              (1∉bs⇒fromBits-bs≡0 bbs 1∉bbs) ]
       1+ ∣ 0# ∣                ≡≤n[ refl ]
       2                         ≤n[ m≤m+n 2 (ln bs) ]
       2 +n ln bs               ≡≤n[ cong 1+_ (sym (length-xs:x 1b bs)) ]
       1+ (ln (bs ∷ʳ 1b))       ≡≤n[ refl ]
       ∣ bbs 1# ∣
     ≤nEnd

  aux (yes 1∈bbs) =  
      ≤nBegin 
        1+ ∣ (bbs 1#) ∸ 2^ (1+ ln bs) ∣   ≡≤n[ cong (1+_ ∘ ∣_∣) 
                                                 (∸∘2^∘ln≗fromBits (b ∷ bs)) ]
        1+ ∣ fromBits bbs ∣      ≤n[ s≤s (1∈bs⇒|fromBits-bs|≤|bs| bbs 1∈bbs) ]
        1+ ln bbs               ≡≤n[ sym (length-xs:x 1b bbs) ]
        ln (bbs ∷ʳ 1b)          ≡≤n[ refl ]
        ∣ bbs 1# ∣
      ≤nEnd


------------------------------------------------------------------------------
|bbs1|≤|y|⇒|bbs1∸y|<|bbs1| :  
                 ∀ b bs y → let bbs = b ∷ bs
                            in
                            ∣ bbs 1# ∣ ≤n ∣ y ∣ → ∣ bbs 1# ∸ y ∣ <n ∣ bbs 1# ∣
-- The order is decreased if 
-- minuend > 1  and  order(minuend) ≤ order(subtrahend). 

|bbs1|≤|y|⇒|bbs1∸y|<|bbs1| b bs 0# |bbs1|≤1 =  ⊥-elim (|bbs1|≰1 |bbs1|≤1)
       where
       1<|bbs1| = ≤nBegin 
                    2                 ≤n[ m≤m+n 2 (ln bs) ]
                    2 +n (ln bs)     ≡≤n[ cong 1+_ (sym (length-xs:x 1b bs)) ]
                    1+ ∣ bs 1# ∣     ≡≤n[ refl ]
                    ∣ (b ∷ bs) 1# ∣ 
                  ≤nEnd 

       |bbs1|≰1 = NProp.<⇒≱ 1<|bbs1|

|bbs1|≤|y|⇒|bbs1∸y|<|bbs1| b bs ([] 1#) |bbs1|≤1 =  ⊥-elim (|bbs1|≰1 |bbs1|≤1)
       where
       1<|bbs1| = ≤nBegin 
                    2                 ≤n[ m≤m+n 2 (ln bs) ]
                    2 +n (ln bs)     ≡≤n[ cong 1+_ (sym (length-xs:x 1b bs)) ]
                    1+ ∣ bs 1# ∣     ≡≤n[ refl ]
                    ∣ (b ∷ bs) 1# ∣ 
                  ≤nEnd 

       |bbs1|≰1 = NProp.<⇒≱ 1<|bbs1|

|bbs1|≤|y|⇒|bbs1∸y|<|bbs1| b bs ((b' ∷ bs') 1#) |bbs1|≤|b'bs'1| =  
  case                                              
      NatProp0.≤⇒⊎ |bbs1|≤|b'bs'1| 
  of \ 
  { (inj₁ |bbs1|<|b'bs'1|) → 
         let 
           bbs = b ∷ bs;  b'bs' = b' ∷ bs';  bbs1 = bbs 1#;  b'bs'1 = b'bs' 1#

           bbs1<b'bs'1 =  inj₁ |bbs1|<|b'bs'1|
         in    
         ≤nBegin 
           1+ ∣ bbs1 ∸ b'bs'1 ∣ 
                          ≡≤n[ cong (1+_ ∘ ∣_∣) 
                                (x≤y⇒x∸y≡0 {bbs1} {b'bs'1} (inj₁ bbs1<b'bs'1)) 
                             ]
           1+ ∣ 0# ∣      ≡≤n[ refl ]
           2               ≤n[ m≤m+n 2 (ln bs) ]
           2 +n ln bs     ≡≤n[ cong 1+_ (sym (length-xs:x 1b bs)) ]
           1+ ∣ bs 1# ∣   ≡≤n[ refl ]
           ∣ bbs 1# ∣
         ≤nEnd

  ; (inj₂ |bbs1|≡|b'bs'1|) → 
      let
        bbs   = b ∷ bs;     bbs1   = bbs 1#   
        b'bs' = b' ∷ bs';   b'bs'1 = b'bs' 1# 

        <b'bs'>   = fromBits b'bs';   2^|bbs| = 2^ (ln bbs)
        2^|b'bs'| = 2^ (ln b'bs')

        |bbs|≡|b'bs'| = 
             begin≡ 
               ln bbs             ≡⟨ cong predN (sym (length-xs:x 1b bbs)) ⟩
               predN ∣ bbs1 ∣     ≡⟨ cong predN (|bbs1|≡|b'bs'1|) ⟩
               predN ∣ b'bs'1 ∣   ≡⟨ cong predN (length-xs:x 1b b'bs') ⟩
               ln b'bs'
             end≡
      in
      ≤nBegin 
        1+ ∣ bbs1 ∸ b'bs'1 ∣               ≡≤n[ cong (1+_ ∘ ∣_∣ ∘ (bbs1 ∸_)) 
                                                     (partHighest-2^ b'bs') 
                                              ]
        1+ ∣ bbs1 ∸ (<b'bs'> + 2^|b'bs'|) ∣  ≡≤n[ cong (1+_ ∘ ∣_∣ ∘ (bbs1 ∸_)) 
                                                  (+-comm <b'bs'> 2^|b'bs'|) ]
        1+ ∣ bbs1 ∸ (2^|b'bs'| + <b'bs'>) ∣ 
                             ≡≤n[ cong (\n → 1+ ∣ bbs1 ∸ (2^ n + <b'bs'>) ∣)
                                                         (sym |bbs|≡|b'bs'|) ]
        1+ ∣ bbs1 ∸ (2^|bbs| + <b'bs'>) ∣  
                                 ≡≤n[ cong (1+_ ∘ ∣_∣)
                                        (sym (∸-+-assoc bbs1 2^|bbs| <b'bs'>))
                                    ]
        1+ ∣ (bbs1 ∸ 2^|bbs|) ∸ <b'bs'> ∣  
                                         ≤n[ s≤s (|x∸y|≤|x| (bbs1 ∸ 2^|bbs|) 
                                                                    <b'bs'>) ]
        1+ ∣ (bbs1 ∸ 2^|bbs|) ∣          ≤n[ |bbs1∸2^1+|bs||<|bbs1| b bs ]
        ∣ bbs 1# ∣
      ≤nEnd
  }

------------------------------------------------------------------------------
|2^[1+n]∸bs1|<|2^[1+n]| :  ∀ n bs → ∣ (2^ (1+ n)) ∸ (bs 1#) ∣ <n ∣ 2^ (1+ n) ∣
|2^[1+n]∸bs1|<|2^[1+n]| n bs = 
  ≤nBegin 
    1+ ∣ (2^ n') ∸ (bs 1#) ∣   ≡≤n[ cong (1+_ ∘ ∣_∣ ∘ ((2^ n') ∸_)) bs1≡1+pbs1
                                  ]
    1+ ∣ (2^ n') ∸ (1' + pbs1) ∣   ≡≤n[ cong (1+_ ∘ ∣_∣) 
                                             (sym (∸-+-assoc (2^ n') 1' pbs1)) 
                                      ] 
    1+ ∣ ((2^ n') ∸ 1') ∸ pbs1 ∣   ≡≤n[ cong (1+_ ∘ ∣_∣ ∘ (_∸ pbs1)) 
                                                          (∸1≗pred (2^ n')) ]
    1+ ∣ (pred (2^ n')) ∸ pbs1 ∣    ≤n[ s≤s (|x∸y|≤|x| (pred (2^ n')) pbs1) ]
    1+ ∣ pred (2^ n') ∣             ≤n[ |pred-2^[1+n]|<|2^[1+n]| n ]
    ∣ 2^ (1+ n) ∣
  ≤nEnd 
  where
  n' = 1+ n;  bs1 = bs 1#;  pbs1 = pred bs1;  bs1≡1+pbs1 = sym (suc∘pred bs)


------------------------------------------------------------------------------
y≤x,y*2>x⇒|x∸y|<n|x| :  ∀ b bs y → let x = (b ∷ bs) 1#
                                   in
                                   y ≤ x → y *2 > x → ∣ x ∸ y ∣ <n ∣ x ∣ 

-- A certain case when ∸ decreases the order of the minuend. 
-- (used in the proof for  divMod).

y≤x,y*2>x⇒|x∸y|<n|x| b bs y (inj₂ y≡bbs1) _ =  
  ≤nBegin 
    1+ ∣ bbs1 ∸ y ∣  ≡≤n[ cong (1+_ ∘ ∣_∣) (x≤y⇒x∸y≡0 (inj₂ (sym y≡bbs1))) ]
    1+ ∣ 0# ∣        ≡≤n[ refl ] 
    2                 ≤n[ m≤m+n 2 (ln bs) ]
    2 +n ln bs       ≡≤n[ cong 1+_ (sym (length-xs:x 1b bs)) ] 
    1+ ∣ bs 1# ∣     ≡≤n[ refl ] 
    ∣ bbs1 ∣ 
  ≤nEnd
  where bbs1 = (b ∷ bs) 1#

y≤x,y*2>x⇒|x∸y|<n|x| b bs 0# _ 0*2>bbs1 =  ⊥-elim (0*2≯bbs1 0*2>bbs1)
                                           where
                                           0*2≯bbs1 = ≮0 ((b ∷ bs) 1#)
                          
y≤x,y*2>x⇒|x∸y|<n|x| b bs (bsY 1#) (inj₁ y<bbs1) y*2>bbs1 =  
                                      aux (compareN ∣ y ∣ ∣ bbs1 ∣) <bbs> refl
  where
  y     = bsY 1#;        bsY1   = bsY 1#;              |bs|    = ln bs
  |bbs| = ln (b ∷ bs);   <bbs>  = fromBits (b ∷ bs);   2^|bbs| = 2^ |bbs|
  bbs1  = (b ∷ bs) 1#;   |bbs1| = ∣ bbs1 ∣;            |y|     = ∣ y ∣ 

  0<y       =  0<bs1 bsY  
  1≤y       =  <⇒suc≤ {0#} {y} 0<y
  2^|bbs|≢0 =  >⇒≢ {2^|bbs|} (0<2^ |bbs|)

  bbs1≡<bbs>+2^|bbs| :  bbs1 ≡ <bbs> + 2^ |bbs|
  bbs1≡<bbs>+2^|bbs| =  partHighest-2^ (b ∷ bs)

  -----------------------------------------------------------
  aux :  Tri (|y| <n |bbs1|) (|y| ≡ |bbs1|) (|y| >n |bbs1|) → 
                             (x' : Bin) → x' ≡ <bbs> → ∣ bbs1 ∸ y ∣ <n |bbs1|

  aux (tri> _ _ |y|>|bbs1|) _ _ =  ⊥-elim (<-asym {y} {bbs1} y<bbs1 y>bbs1)
                                   where
                                   y>bbs1 = inj₁ |y|>|bbs1|

  aux (tri≈ _ |y|≡|bbs1| _) _ _ = 
                                |bbs1|≤|y|⇒|bbs1∸y|<|bbs1| b bs y |bbs1|≤|y|
                                where
                                |bbs1|≤|y| = ≤n-reflexive (sym |y|≡|bbs1|)
  
  aux (tri< |y|<|bbs1| _ _) 0# 0≡<bbs> =       -- here  bbs1 = 2^ |bbs1|
    ≤nBegin
      1+ ∣ bbs1 ∸ y ∣     ≡≤n[ cong (1+_ ∘ ∣_∣ ∘ (_∸ y)) bbs1≡2^|bbs| ]
      1+ ∣ 2^|bbs| ∸ y ∣   ≤n[ |2^[1+n]∸bs1|<|2^[1+n]| |bs| bsY ]
      ∣ 2^|bbs| ∣         ≡≤n[ |2^n|≡1+n |bbs| ] 
      1+ |bbs|            ≡≤n[ sym (length-xs:x 1b (b ∷ bs)) ] 
      |bbs1|
    ≤nEnd
    where
    bbs1≡2^|bbs| =  
           begin≡ bbs1                 ≡⟨ bbs1≡<bbs>+2^|bbs| ⟩
                  <bbs> + (2^ |bbs|)   ≡⟨ cong (_+ (2^ |bbs|)) (sym 0≡<bbs>) ⟩
                  0# + (2^ |bbs|)      ≡⟨ 0+ (2^ |bbs|) ⟩
                  2^ |bbs|
           end≡

    2^|bbs|∸y<2^|bbs| =  
                      begin 2^|bbs| ∸ y   ≤[ ∸-mono-≤ (≤-refl {2^|bbs|}) 1≤y ] 
                            2^|bbs| ∸ 1'  ≡[ ∸1≗pred 2^|bbs| ] 
                            pred 2^|bbs|  <[ pred< 2^|bbs|≢0 ] 
                            2^|bbs|
                      ∎

  aux (tri< |y|<|bbs1| _ _) (bs' 1#) bs'1≡<bbs> =  aux' (y ∸ <bbs>) refl
    where
    <bbs>*2<bbs1 = 
          begin
            <bbs> *2             ≡[ *2≗+ <bbs> ]
            <bbs> + <bbs>        <[ +-mono-≤-< {<bbs>} {_} {<bbs>} {2^ |bbs|}
                                            ≤-refl (fromBits-bbs<2^|bbs| b bs)
                                  ]
            <bbs> + (2^ |bbs|)   ≡[ sym bbs1≡<bbs>+2^|bbs| ]
            bbs1
          ∎

    <bbs>-<-y =  
          case y ≤? <bbs>
          of \ 
          { (no y≰bbs)  → ≰⇒> y≰bbs
          ; (yes y≤bbs) → let y*2<bbs1 = begin y *2       ≤[ *2-mono-≤ y≤bbs ]
                                               <bbs> *2   <[ <bbs>*2<bbs1 ]
                                               bbs1
                                         ∎
                          in  ⊥-elim (<-asym {y *2} {bbs1} y*2<bbs1 y*2>bbs1)
          }

    aux' :  (d : Bin) → d ≡ y ∸ <bbs> → ∣ bbs1 ∸ y ∣ <n |bbs1|

    aux' 0# 0≡y∸<bbs> =  ⊥-elim (≤⇒≯ y*2≤bbs1 y*2>bbs1)
                        where
                        y≤<bbs>     = x∸y≡0⇒x≤y {y} {<bbs>} (sym 0≡y∸<bbs>)
                        y*2≤<bbs>*2 = *2-mono-≤ y≤<bbs> 
                        y*2≤bbs1    = ≤-trans {y *2} {<bbs> *2} {bbs1} 
                                              y*2≤<bbs>*2 (inj₁ <bbs>*2<bbs1)

    aux' (ds 1#) d≡y∸<bbs> = 
      ≤nBegin 
        1+ ∣ bbs1 ∸ y ∣      ≡≤n[ cong (1+_ ∘ ∣_∣ ∘ (_∸ y)) bbs1≡<bbs>+2^|bbs| 
                                ]
        1+ ∣ (<bbs> + 2^|bbs|) ∸ y ∣  
                     ≡≤n[ cong (1+_ ∘ ∣_∣)
                          (cong₂ _∸_ (+-comm <bbs> (2^|bbs|)) (sym <bbs>+d≡y))
                        ]
        1+ ∣ (2^|bbs| + <bbs>) ∸ (<bbs> + d) ∣
                              ≡≤n[ cong (1+_ ∘ ∣_∣)
                                   (sym (∸-+-assoc (2^|bbs| + <bbs>) <bbs> d))
                                 ]
        1+ ∣ ((2^|bbs| + <bbs>) ∸ <bbs>) ∸ d ∣  
                      ≡≤n[ cong (1+_ ∘ ∣_∣ ∘ (_∸ d)) ([x+y]∸y≡x 2^|bbs| <bbs>)
                         ]
        1+ ∣ 2^|bbs| ∸ d ∣           ≡≤n[ refl ]
        1+ ∣ 2^ (1+ |bs|) ∸ d ∣       ≤n[ |2^[1+n]∸bs1|<|2^[1+n]| |bs| ds ]
        ∣ 2^ (1+ |bs|) ∣             ≡≤n[ refl ]
        ∣ 2^ |bbs| ∣                 ≡≤n[ |2^n|≡1+n |bbs| ]
        1+ |bbs|                     ≡≤n[ sym (length-xs:x 1b (b ∷ bs)) ]
        ∣ bbs1 ∣ 
      ≤nEnd
      where
      d         = ds 1#
      <bbs>+d≡y =  
           begin≡ 
             <bbs> + d             ≡⟨ cong (<bbs> +_) d≡y∸<bbs> ⟩
             <bbs> + (y ∸ <bbs>)   ≡⟨ x+[y∸x]≡y {<bbs>} {y} (inj₁ <bbs>-<-y) ⟩
             y
           end≡
