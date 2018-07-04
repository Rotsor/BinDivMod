{-                                                            
This file is a part of the library  Binary-3.1.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.  

Binary-3.1  is free software: you can redistribute it and/or modify it 
under the terms of the GNU General Public License.
See  license.txt.
-}

module Bin3 where

open import Function using (_∘_; _$_)
import Algebra.FunctionProperties as FuncProp
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PE using 
                                     (_≡_; _≗_; subst; cong; cong₂; refl; sym)
open PE.≡-Reasoning
open import Data.Empty   using (⊥-elim)
open import Data.Product using (_,_; ∃)
open import Data.Digit   using (Bit)
open import Data.List    using (List; []; _∷_; _∷ʳ_; [_]; replicate)
                         renaming (length to ln)
open import Data.List.Properties using (length-replicate)
open import Data.Nat using (ℕ; s≤s; z≤n) 
                     renaming (suc to 1+_; pred to predN; _≤_ to _≤n_; 
                               _<_ to _<n_; _+_ to _+n_; _*_ to _*n_;
                               _^_ to _^n_
                              )
open import Data.Nat.Properties as NProp using (m≤m+n; module ≤-Reasoning) 
     renaming 
            (≤-refl to ≤n-refl; ≤-reflexive to ≤n-reflexive; 
             +-comm to +n-comm; +-assoc to +n-assoc; 
             pred-mono to predN-mono; *-comm to *n-comm; 
             *-assoc to *n-assoc; *-distribʳ-+ to *n-rDistrib; 
             *-distribˡ-+ to *n-lDistrib
            )                                
open ≤-Reasoning using () renaming (begin_ to ≤begin_; _∎ to _≤end;
                                          _≡⟨_⟩_ to _≡≤[_]_; _≤⟨_⟩_ to _≤[_]_)

-- of application --- 
open import List0    using (length-xs:x)
open import NatProp0 using (1*; suc≢0; <⇒≱; 0<1+n)
open import Bin0 using (Bin; suc; 0b; 1b; ⊥b; _+_; pred; _<_; _*2; 2^_; _∣_; 
                        shift; toℕ; toBits; fromBits; addBL; _*_; *aux; _∈_; 
                        _∈?_; predList; _≡b_; const-1b
                       )
                 renaming (1bin to 1'; 2bin to 2')

open import Bin1 using (∣_∣; *2≗2bin*; 2^suc; |2^n|≡1+n; fromBits-0:bs-as*2; 
                                              toBits-2^; 1∉bs⇒fromBits-bs≡0)
open import Bin2 using 
     (+0; 0+; hasLast1-bs:1; suc-even1; x1#+x1#-asShift; init-x1+y1; fromℕ; 
      suc∘pred; 0<toℕ-bs1; fromBits-bs:1; toℕ∘fromℕ; fromℕ∘toℕ; +-assoc; 
      +-comm; toℕ+homo; toℕ-suc-homo; fromBits-1:bs-as-suc*2; toBits∘fromBits;
      predList<0:zeroes:1>; predList[repl-0]:1      
     )



--****************************************************************************
-- This module povides proofs for various statements for 
-- product of binary numbers.

open Bin

private module FP-Bin = FuncProp (_≡_ {A = Bin})


*0 :  ∀ x → x * 0# ≡ 0#

*0 0#            = refl
*0 ([] 1#)       = refl
*0 ((b ∷ bs) 1#) = 
          begin ((b ∷ bs) 1#) * 0#         ≡⟨ refl ⟩
                *aux b 0# ((bs 1#) * 0#)   ≡⟨ cong (*aux b 0#) (*0 (bs 1#)) ⟩
                *aux b 0# 0#               ≡⟨ refl ⟩
                0#
          ∎

----------------------
*1 :  ∀ x → x * 1' ≡ x

*1 0#             = refl
*1 ([] 1#)        = refl
*1 ((⊥b ∷ _) 1#)
*1 ((0b ∷ bs) 1#) = 
         begin ((0b ∷ bs) 1#) * ([] 1#)              ≡⟨ refl ⟩
               *aux 0b ([] 1#) ((bs 1#) * ([] 1#))   ≡⟨ cong (*aux 0b 1') 
                                                             (*1 (bs 1#)) ⟩
               *aux 0b ([] 1#) (bs 1#)               ≡⟨ refl ⟩
               (0b ∷ bs) 1#
         ∎
*1 ((1b ∷ bs) 1#) = 
          begin
            ((1b ∷ bs) 1#) * 1'          ≡⟨ refl ⟩
            *aux 1b 1' ((bs 1#) * 1')    ≡⟨ cong (*aux 1b 1') (*1 (bs 1#)) ⟩
            *aux 1b 1' (bs 1#)           ≡⟨ refl ⟩
            1' + ((0b ∷ bs) 1#)          ≡⟨ suc-even1 bs ⟩
            (1b ∷ bs) 1#
          ∎

-----------------------------------------------------------------
init-x1*y1 :  ∀ bs bs' → (∃ \bs'' → (bs 1#) * (bs' 1#) ≡ bs'' 1#)
--
-- This means actually  HasLast1 (toBits ((bs 1#) * (bs' 1#))).
-- Also this means:     ∀ a b → a > 0 → b > 0 → a * b > 0.

init-x1*y1 []        bs' =  (bs' , refl) 
init-x1*y1 (⊥b ∷ bs) 
init-x1*y1 (0b ∷ bs) bs' = 
  let 
    (bs'' , eq0) = init-x1*y1 bs bs'  

    eq :  ((0b ∷ bs) 1#) * (bs' 1#) ≡ (0b ∷ bs'') 1#
    eq =  
      begin
        ((0b ∷ bs) 1#) * (bs' 1#)               ≡⟨ refl ⟩ 
        *aux 0b (bs' 1#) ((bs 1#) * (bs' 1#))   ≡⟨ cong (*aux 0b (bs' 1#)) 
                                                                      eq0 ⟩ 
        *aux 0b (bs' 1#) (bs'' 1#)              ≡⟨ refl ⟩ 
        (0b ∷ bs'') 1#
      ∎
  in
  (0b ∷ bs'' , eq)

init-x1*y1 (1b ∷ bs) bs' =  
  let
    (bs'' , eq0) = init-x1*y1 bs bs'
    (bs₃ , eq1)  = init-x1+y1 bs' (0b ∷ bs'')
  
    eq :  ((1b ∷ bs) 1#) * (bs' 1#) ≡ bs₃ 1#
    eq = 
       begin
         ((1b ∷ bs) 1#) * (bs' 1#)               ≡⟨ refl ⟩ 
         *aux 1b (bs' 1#) ((bs 1#) * (bs' 1#))   ≡⟨ cong (*aux 1b (bs' 1#)) 
                                                                       eq0 ⟩ 
         *aux 1b (bs' 1#) (bs'' 1#)              ≡⟨ refl ⟩ 
         (bs' 1#) + ((0b ∷ bs'') 1#)             ≡⟨ eq1 ⟩ 
         bs₃ 1#
       ∎
  in
  (bs₃ , eq)

*aux-0-x-x1*y1 :  ∀ x bs bs' → 
                         *aux 0b x (bs 1# * bs' 1#) ≡ 2' * (bs 1# * bs' 1#)
*aux-0-x-x1*y1 x bs bs' =  
            let (bs'' , eq) = init-x1*y1 bs bs'
            in
            begin *aux 0b x (bs 1# * bs' 1#)   ≡⟨ cong (*aux 0b x) eq ⟩ 
                  *aux 0b x (bs'' 1#)          ≡⟨ refl ⟩ 
                  2' * (bs'' 1#)               ≡⟨ cong (2' *_) (sym eq) ⟩ 
                  2' * (bs 1# * bs' 1#)   
            ∎ 

----------------------------------
*2-as+ :  (x : Bin) → x *2 ≡ x + x
*2-as+ 0#      = refl
*2-as+ (bs 1#) = sym (x1#+x1#-asShift bs)

2bin*as+ :  (x : Bin) → 2' * x ≡ x + x
2bin*as+ x =  
           begin 2' * x    ≡⟨ sym (*2≗2bin* x) ⟩
                 x *2      ≡⟨ *2-as+ x ⟩
                 x + x
           ∎

private -- auxiliary lemmata ------------------------------------------------- 
        -- for proving commutativity, associativity and distributivity 
        -- for _*_ 

  2bin*comm :  ∀ x → 2' * x ≡ x * 2'
  2bin*comm x = 
              aux x (ln (toBits x)) refl
    where
    aux : (x : Bin) → (n : ℕ) → n ≡ (ln (toBits x)) → 2' * x ≡ x * 2'

                         -- the last two arguments serve for termination proof
    aux 0#      _ _ =  refl 
    aux ([] 1#) _ _ =  refl
    aux ((⊥b ∷ _)  1#) 
    aux ((_ ∷ _) 1#)   0      0≡k        =  ⊥-elim (suc≢0 (sym 0≡k))
    aux ((0b ∷ bs) 1#) (1+ n) n'≡|0bs#1| = 
      begin 
        2' * (0bs 1#)                           ≡⟨ sym (*2≗2bin* (0bs 1#)) ⟩ 
        (0bs 1#) *2                             ≡⟨ refl ⟩ 
        (0b ∷ 0bs) 1#                           ≡⟨ refl ⟩ 
        *aux 0b ((0b ∷ []) 1#) ((0b ∷ bs) 1#)   
                                              ≡⟨ cong (*aux 0b ((0b ∷ []) 1#))
                                                          (*2≗2bin* (bs 1#)) ⟩ 
        *aux 0b ((0b ∷ []) 1#) (2' * (bs 1#))   
                                              ≡⟨ cong (*aux 0b ((0b ∷ []) 1#))
                                                    (aux (bs 1#) n n≡|bs#1|) ⟩
        *aux 0b ((0b ∷ []) 1#) ((bs 1#) * 2')   ≡⟨ refl ⟩ 
        ((0b ∷ bs) 1#) * ((0b ∷ []) 1#)
      ∎
      where 
      0bs      = 0b ∷ bs
      n≡|bs#1| = cong predN n'≡|0bs#1|

    aux ((1b ∷ bs) 1#) (1+ n) n'≡|1bs#1| = 
      begin 
        2' * (1bs 1#)                    ≡⟨ sym (*2≗2bin* (1bs 1#)) ⟩ 
        (1bs 1#) *2                      ≡⟨ refl ⟩ 
        (0b ∷ 1b ∷ bs) 1#                ≡⟨ sym (fromBits-bs:1 (0b ∷ 1b ∷ bs)) 
                                          ⟩ 
        ((0b ∷ []) 1#) + ((0b ∷ 0b ∷ bs) 1#)    ≡⟨ refl ⟩ 
        *aux 1b ((0b ∷ []) 1#) ((0b ∷ bs) 1#)   
                                              ≡⟨ cong (*aux 1b ((0b ∷ []) 1#))
                                                      (sym (*2≗2bin* (bs 1#))) 
                                               ⟩ 
        *aux 1b ((0b ∷ []) 1#) (2' * (bs 1#))  
                                              ≡⟨ cong (*aux 1b ((0b ∷ []) 1#))
                                                    (aux (bs 1#) n n≡|bs#1|) ⟩ 
        *aux 1b ((0b ∷ []) 1#) ((bs 1#) * 2')   ≡⟨ refl ⟩ 
        ((1b ∷ bs) 1#) * ((0b ∷ []) 1#)
      ∎
      where 
      1bs      = 1b ∷ bs
      n≡|bs#1| = cong predN n'≡|1bs#1|


  ----------------------------------------------------------------------------
  distrib-suc*2 :  _*2 ∘ suc ≗ (2' +_) ∘ _*2
  distrib-suc*2 x = 
    begin
      (suc x) *2             ≡⟨ *2-as+ (suc x) ⟩ 
      (1' + x) + (1' + x)    ≡⟨ +-assoc 1' x (1' + x) ⟩ 
      1' + (x + (1' + x))    ≡⟨ cong suc (sym (+-assoc x 1' x)) ⟩ 
      1' + ((x + 1') + x)    ≡⟨ cong (suc ∘ (_+ x)) (+-comm x 1') ⟩ 
      1' + ((1' + x) + x)    ≡⟨ cong suc (+-assoc 1' x x) ⟩ 
      1' + (1' + (x + x))    ≡⟨ sym (+-assoc 1' 1' (x + x)) ⟩ 
      (1' + 1') + (x + x)    ≡⟨ cong (2' +_) (sym (*2-as+ x)) ⟩ 
      2' + (x *2)
    ∎

  2bin*suc-distrib :  ∀ x → 2' * suc x ≡ 2' + 2' * x
  2bin*suc-distrib x =  
                     begin 2' * suc x       ≡⟨ sym (*2≗2bin* (suc x)) ⟩  
                           (suc x) *2       ≡⟨ distrib-suc*2 x ⟩  
                           2' + x *2        ≡⟨ cong (2' +_) (*2≗2bin* x) ⟩
                           2' + 2' * x
                     ∎

  ----------------------------------------------------------------------------
  2bin*distrib :  ∀ x y → 2' * (x + y) ≡  2' * x + 2' * y
  2bin*distrib 0# y =  
               begin 2' * (0# + y)       ≡⟨ cong (2' *_) (0+ y) ⟩  
                     2' * y              ≡⟨ sym (0+ (2' * y)) ⟩  
                     0# + 2' * y         ≡⟨ cong (_+ (2' * y)) (sym (*0 2')) ⟩
                     2' * 0# + (2' * y)
               ∎

  2bin*distrib (bs 1#) y =  
    begin 
      2' * (bs 1# + y)             ≡⟨ cong ((2' *_) ∘ (_+ y)) bs#1≡suc-x ⟩  
      2' * (suc x + y)             ≡⟨ cong (2' *_) (+-assoc 1' x y) ⟩  
      2' * (suc x+y)               ≡⟨ 2bin*as+ (suc x+y) ⟩  
      suc x+y + suc x+y            ≡⟨ cong₂ _+_ (sym (+-assoc 1' x y))
                                                (sym (+-assoc 1' x y)) 
                                    ⟩  
      (suc x + y) + (suc x + y)    ≡⟨ +-assoc (suc x) y (suc x + y) ⟩  
      suc x + (y + (suc x + y))    ≡⟨ cong ((suc x) +_) 
                                           (+-comm y (suc x + y)) ⟩  
      suc x + ((suc x + y) + y)    ≡⟨ cong ((suc x) +_) 
                                           (+-assoc (suc x) y y) ⟩  
      suc x + (suc x + (y + y))    ≡⟨ sym (+-assoc (suc x) (suc x) (y + y)) ⟩  
      (suc x + suc x) + (y + y)    ≡⟨ cong₂ _+_ (sym (2bin*as+ (suc x)))
                                                (sym (2bin*as+ y)) 
                                    ⟩  
      2' * (suc x) + 2' * y        ≡⟨ cong (\z → 2' * z + 2' * y)
                                           (sym bs#1≡suc-x) ⟩  
      2' * (bs 1#) + 2' * y
    ∎
    where
    x = pred (bs 1#);   x+y = x + y

    bs#1≡suc-x :  bs 1# ≡ suc x
    bs#1≡suc-x =  sym (suc∘pred bs)


  ----------------------------------------------------
  *2-assoc :  (x y : Bin) → (x *2) * y ≡ (x * y) *2 

  *2-assoc 0# _  =  refl 
  *2-assoc x  0# =  begin (x *2) * 0#    ≡⟨ *0 (x *2) ⟩ 
                          0#             ≡⟨ refl ⟩ 
                          0# *2          ≡⟨ cong _*2 (sym (*0 x)) ⟩ 
                         (x * 0#) *2 
                    ∎
  *2-assoc (bs 1#) (bs' 1#) = 
    let
      (bs'' , eq0) = init-x1*y1 bs bs'     
    in
    begin
      ((bs 1#) *2) * (bs' 1#)                 ≡⟨ refl ⟩ 
      ((0b ∷ bs) 1#) * (bs' 1#)               ≡⟨ refl ⟩ 
      *aux 0b (bs' 1#) ((bs 1#) * (bs' 1#))   ≡⟨ cong (*aux 0b (bs' 1#)) eq0 ⟩ 
      *aux 0b (bs' 1#) (bs'' 1#)              ≡⟨ refl ⟩  
      (0b ∷ bs'') 1#                          ≡⟨ refl ⟩ 
      (bs'' 1#) *2                            ≡⟨ cong _*2 (sym eq0) ⟩ 
      ((bs 1#) * (bs' 1#)) *2 
    ∎


  2bin*assoc :  (x y : Bin) → (2' * x) * y ≡ 2' * (x * y)
  2bin*assoc x y = 
                 begin (2' * x) * y     ≡⟨ cong (_* y) $ sym (*2≗2bin* x) ⟩ 
                       (x *2) * y       ≡⟨ *2-assoc x y ⟩ 
                       (x * y) *2       ≡⟨ *2≗2bin* (x * y) ⟩ 
                       2' * (x * y)
                 ∎

  --------------------------------------------------------
  2bin*assoc2 :  (x y : Bin) → (x * 2') * y ≡ x * (2' * y)
  2bin*assoc2 0# _  =  refl 
  2bin*assoc2 x  0# =  
                    begin (x * 2') * 0#     ≡⟨ *0 (x * 2') ⟩ 
                          0#                ≡⟨ sym (*0 x) ⟩ 
                          x * 0#            ≡⟨ cong (x *_) (sym (*0 2')) ⟩ 
                          x * (2' * 0#)
                    ∎
  2bin*assoc2 ([] 1#) _               = refl
  2bin*assoc2 ((⊥b ∷ _) 1#)  
  2bin*assoc2 ((0b ∷ bs) 1#) (bs' 1#) = 
    begin 
      (0bs 1# * 2') * (bs' 1#)                     ≡⟨ cong (_* (bs' 1#)) $ 
                                                      sym (2bin*comm (0bs 1#))
                                                    ⟩ 
      00bs 1# * bs' 1#                                       ≡⟨ refl ⟩ 
      *aux 0b (bs' 1#) (0bs 1# * bs' 1#)                     ≡⟨ refl ⟩ 
      *aux 0b (bs' 1#) (*aux 0b (bs' 1#) (bs 1# * bs' 1#))  
                                                ≡⟨ cong (*aux 0b (bs' 1#))
                                                   (*aux-0-x-x1*y1 _ bs bs') ⟩ 
      *aux 0b (bs' 1#) (2' * (bs 1# * bs' 1#))  
                                           ≡⟨ cong (*aux 0b (bs' 1#)) $ sym 
                                                 (2bin*assoc (bs 1#) (bs' 1#))
                                            ⟩ 
      *aux 0b (bs' 1#) (0bs 1# * bs' 1#)    ≡⟨ *aux-0-x-x1*y1 _ 0bs bs' ⟩ 
      2' * (0bs 1# * bs' 1#)                ≡⟨ refl ⟩ 
      2' * ((2' * bs 1#) * bs' 1#)          ≡⟨ cong ((2' *_) ∘ (_* (bs' 1#)))
                                                   (2bin*comm (bs 1#))
                                             ⟩ 
      2' * ((bs 1# * 2') * bs' 1#)          ≡⟨ cong (2' *_)
                                                (2bin*assoc2 (bs 1#) (bs' 1#))
                                             ⟩
      2' * (bs 1# * (2' * bs' 1#))          ≡⟨ refl ⟩ 
      2' * (bs 1# * 0bs' 1#)                ≡⟨ sym (*aux-0-x-x1*y1 _ bs 0bs')
                                             ⟩ 
      *aux 0b (0bs' 1#) (bs 1# * 0bs' 1#)   ≡⟨ refl ⟩ 
      0bs 1# * 0bs' 1#                      ≡⟨ refl ⟩ 
      0bs 1# * (2' * bs' 1#)
    ∎ 
    where
    0bs = 0b ∷ bs;   00bs  = 0b ∷ 0b ∷ bs;   0bs' = 0b ∷ bs'


  2bin*assoc2 ((1b ∷ bs) 1#) (bs' 1#) = 
    let 
      (bs'' , eq0) = init-x1*y1 bs bs'

      0bs = 0b ∷ bs;   1bs  = 1b ∷ bs;    0bs'  = 0b ∷ bs'    
      bs1 = bs 1#;     bs'1 = bs' 1#;     0bs'' = 0b ∷ bs''
    in 
    begin
      (1bs 1# * 2') * bs' 1#                  ≡⟨ cong (_* bs'1) 
                                                 (sym (2bin*comm (1bs 1#))) 
                                               ⟩ 
      (2' * 1bs 1#) * bs' 1#                  ≡⟨ refl ⟩ 
      (0b ∷ 1bs) 1# * bs' 1#                  ≡⟨ refl ⟩ 
      *aux 0b (bs' 1#) (1bs 1# * bs' 1#)      ≡⟨ *aux-0-x-x1*y1 bs'1 1bs bs' ⟩
      2' * (1bs 1# * bs' 1#)                  ≡⟨ refl ⟩ 
      2' * (*aux 1b (bs' 1#) (bs 1# * bs' 1#))
                                        ≡⟨ cong ((2' *_) ∘ (*aux 1b bs'1)) eq0 
                                         ⟩    
      2' * (*aux 1b (bs' 1#) (bs'' 1#))    ≡⟨ refl ⟩ 
      2' * (bs' 1# + 0bs'' 1#)             ≡⟨ 2bin*distrib bs'1 (0bs'' 1#) ⟩
      2' * (bs' 1#) + 2' * 0bs'' 1#        ≡⟨ refl ⟩ 
      0bs' 1# + (0b ∷ 0bs'') 1#            ≡⟨ refl ⟩ 
      *aux 1b (0bs' 1#) (0bs'' 1#)         ≡⟨ refl ⟩ 
      *aux 1b (0bs' 1#) (2' * (bs'' 1#))  
                                         ≡⟨ cong (*aux 1b (0bs' 1#) ∘ (2' *_))
                                                 (sym eq0)
                                          ⟩ 
      *aux 1b (0bs' 1#) (2' * (bs 1# * bs' 1#))
                                              ≡⟨ cong (*aux 1b (0bs' 1#))   
                                                 (sym (2bin*assoc bs1 bs'1)) ⟩ 
      *aux 1b (0bs' 1#) (0bs 1# * bs' 1#) 
                                       ≡⟨ cong (*aux 1b (0bs' 1#) ∘ (_* bs'1))
                                               (2bin*comm bs1)
                                        ⟩ 
      *aux 1b (0bs' 1#) ((bs1 * 2') * bs'1)    ≡⟨ cong (*aux 1b (0bs' 1#))
                                                      (2bin*assoc2 bs1 bs'1) ⟩
      *aux 1b (0bs' 1#) (bs 1# * 0bs' 1#)      ≡⟨ refl ⟩ 
      1bs 1# * (2' * bs' 1#)
    ∎


  ------------------------------------------------------------
  *suc-even :  (x y : Bin) → (suc (x *2)) * y ≡ y + (x *2) * y 

  *suc-even 0# y  =  sym (+0 y)
  *suc-even x  0# =  
               begin (suc (x *2)) * 0#   ≡⟨ *0 (suc (x *2)) ⟩
                     0#                  ≡⟨ refl ⟩
                     0# + 0#             ≡⟨ cong (0# +_) (sym (*0 (x *2))) ⟩
                     0# + (x *2) * 0#
               ∎

  *suc-even (bs 1#) (bs' 1#) = 
    let 
      y            = bs' 1#
      (bs'' , eq0) = init-x1*y1 bs bs'
    in
    begin 
      (suc ((0b ∷ bs) 1#)) * (bs' 1#)         ≡⟨ cong (_* y) (suc-even1 bs) ⟩
      ((1b ∷ bs) 1#) * (bs' 1#)               ≡⟨ refl ⟩
      *aux 1b (bs' 1#) ((bs 1#) * (bs' 1#))   ≡⟨ cong (*aux 1b y) eq0 ⟩
      *aux 1b (bs' 1#) (bs'' 1#)              ≡⟨ refl ⟩
      (bs' 1#) + ((0b ∷ bs'') 1#)             ≡⟨ refl ⟩
      (bs' 1#) + (bs'' 1#) *2                 ≡⟨ cong ((y +_) ∘ _*2) (sym eq0)
                                               ⟩
      (bs' 1#) + ((bs 1#) * (bs' 1#)) *2      ≡⟨ cong ((bs' 1#) +_) $ 
                                                    sym (*2-assoc (bs 1#) y) ⟩
      (bs' 1#) + ((bs 1#) *2) * (bs' 1#)      ≡⟨ refl ⟩
      (bs' 1#) + ((0b ∷ bs) 1#) * (bs' 1#)
    ∎


  -----------------------------------------------
  *suc :  (x y : Bin) → (suc x) * y ≡ y + (x * y) 

  *suc 0#      y  =  *suc-even 0# y 
  *suc (bs 1#) 0# = 
               begin (suc (bs 1#)) * 0#   ≡⟨ *0 (suc (bs 1#)) ⟩
                     0#                   ≡⟨ refl ⟩
                     0# + 0#              ≡⟨ cong (0# +_) $ sym (*0 (bs 1#)) ⟩
                     0# + (bs 1#) * 0# 
               ∎
  *suc ([] 1#)        (bs 1#)  =  sym (x1#+x1#-asShift bs)
  *suc ((⊥b ∷ _) 1#) 
  *suc ((0b ∷ bs) 1#) (bs' 1#) =  *suc-even (bs 1#) (bs' 1#) 
  *suc ((1b ∷ bs) 1#) y        = 
    begin
      (suc (1bs 1#)) * y                 ≡⟨ cong ((_* y) ∘ suc)
                                                 (sym (suc-even1 bs)) 
                                          ⟩
      (1' + (1' + 2' * (bs 1#))) * y     ≡⟨ cong (_* y) $ 
                                            sym (+-assoc 1' 1' (2' * (bs 1#)))
                                          ⟩
      ((1' + 1') + (2' * (bs 1#))) * y   ≡⟨ refl ⟩
      (2' + 2' * (bs 1#)) * y            ≡⟨ cong (\x → (x + 2' * (bs 1#)) * y)
                                                 (sym (*1 2'))   
                                          ⟩
      (2' * 1' + 2' * (bs 1#)) * y       ≡⟨ cong (_* y) $ 
                                            sym (2bin*distrib 1' (bs 1#)) 
                                          ⟩
      (2' * suc (bs 1#)) * y             ≡⟨ 2bin*assoc (suc (bs 1#)) y ⟩
      2' * (suc (bs 1#) * y)             ≡⟨ cong (2' *_) (*suc (bs 1#) y) ⟩
      2' * (y + (bs 1#) * y)             ≡⟨ 2bin*distrib y (bs 1# * y) ⟩
      2' * y + 2' * (bs 1# * y)          ≡⟨ cong (_+ (2' * (bs 1# * y)))
                                                           (2bin*as+ y)
                                          ⟩
      (y + y) + 2' * (bs 1# * y)         ≡⟨ +-assoc y y (2' * (bs 1# * y)) ⟩
      y + (y + 2' * (bs 1# * y))         ≡⟨ cong ((y +_) ∘ (y +_))
                                                 (sym (2bin*assoc (bs 1#) y))
                                          ⟩
      y + (y + ((2' * bs 1#) * y))       ≡⟨ refl ⟩
      y + (y + (0bs 1# * y))             ≡⟨ cong (y +_) $ 
                                            (sym (*suc-even (bs 1#) y)) 
                                          ⟩
      y + (suc (0bs 1#) * y)             ≡⟨ cong ((y +_) ∘ (_* y)) 
                                                           (suc-even1 bs) ⟩
      y + (1bs 1#) * y
    ∎
    where
    1bs = 1b ∷ bs;   0bs = 0b ∷ bs  


------------------------------------------------------------------------------
toℕ*homo :  ∀ a b → toℕ (a * b) ≡ toℕ a *n toℕ b
toℕ*homo a b = 
             aux a b (toℕ a) refl
  where
  aux :  ∀ a b cnt → cnt ≡ toℕ a →  toℕ (a * b) ≡ toℕ a *n toℕ b

  -- The last two arguments present the counter used in termination proof.

  aux 0#      _ _  _       =  refl
  aux (bs 1#) _ 0  0≡toN-a =  ⊥-elim (0≢toN-a 0≡toN-a) 
                              where
                              0≢toN-a = NProp.<⇒≢ (0<toℕ-bs1 bs)

  aux (bs 1#) y (1+ cnt) cnt'≡toℕ-x = 
    begin 
      toℕ (x * y)                ≡⟨ cong (toℕ ∘ (_* y)) (sym suc-px≡x) ⟩ 
      toℕ (suc px * y)           ≡⟨ cong toℕ (*suc px y) ⟩ 
      toℕ (y + px * y)           ≡⟨ toℕ+homo y (px * y) ⟩ 
      yN +n toℕ (px * y)         ≡⟨ cong (yN +n_) (aux px y cnt cnt≡pxN) ⟩ 
      yN +n (pxN *n yN)          ≡⟨ cong (_+n (pxN *n yN)) (sym (1* yN)) ⟩ 
      (1 *n yN) +n (pxN *n yN)   ≡⟨ sym (*n-rDistrib yN 1 pxN) ⟩ 
      (1 +n pxN) *n yN           ≡⟨ cong (_*n yN) (sym (toℕ+homo 1' px)) ⟩ 
      (toℕ (1' + px)) *n yN      ≡⟨ cong ((_*n yN) ∘ toℕ) suc-px≡x ⟩ 
      (toℕ x) *n yN             
    ∎
    where
    x = bs 1#;   px = pred x;  xN = toℕ x;  pxN = toℕ px;  yN = toℕ y

    suc-px≡x = suc∘pred bs

    cnt≡pxN :  cnt ≡ toℕ (pred x)
    cnt≡pxN =  
        begin 
          cnt                    ≡⟨ refl ⟩
          predN (1+ cnt)         ≡⟨ cong predN cnt'≡toℕ-x ⟩
          predN (toℕ x)          ≡⟨ cong (predN ∘ toℕ) (sym suc-px≡x) ⟩
          predN (toℕ (suc px))   ≡⟨ cong predN (toℕ-suc-homo px) ⟩  
          predN (1+ (toℕ px))    ≡⟨ refl ⟩
          toℕ px
        ∎

fromℕ*homo :  ∀ m n → fromℕ (m *n n) ≡ fromℕ m * fromℕ n
fromℕ*homo m n = 
           begin
             fromℕ (m *n n)           ≡⟨ cong fromℕ (cong₂ _*n_ m≡aN n≡bN) ⟩
             fromℕ (toℕ a *n toℕ b)   ≡⟨ cong fromℕ (sym (toℕ*homo a b)) ⟩
             fromℕ (toℕ (a * b))      ≡⟨ fromℕ∘toℕ (a * b) ⟩
             a * b
           ∎
           where
           a    = fromℕ m;            b    = fromℕ n
           m≡aN = sym (toℕ∘fromℕ m);  n≡bN = sym (toℕ∘fromℕ n)

------------------------------------------------------------------------------
*-comm : FP-Bin.Commutative _*_

*-comm a b =  begin a * b                 ≡⟨ sym (fromℕ∘toℕ (a * b)) ⟩
                    fromℕ (toℕ (a * b))   ≡⟨ cong fromℕ (toℕ*homo a b) ⟩
                    fromℕ (aN *n bN)      ≡⟨ cong fromℕ (*n-comm aN bN) ⟩
                    fromℕ (bN *n aN)      ≡⟨ cong fromℕ (sym (toℕ*homo b a)) ⟩
                    fromℕ (toℕ (b * a))   ≡⟨ fromℕ∘toℕ (b * a) ⟩
                    b * a
              ∎
              where  
              aN = toℕ a;  bN = toℕ b

*-assoc : FP-Bin.Associative _*_
*-assoc a b c = 
  begin 
    (a * b) * c                  ≡⟨ sym (fromℕ∘toℕ ((a * b) * c)) ⟩
    fromℕ (toℕ ((a * b) * c))    ≡⟨ cong fromℕ (toℕ*homo (a * b) c) ⟩
    fromℕ (toℕ (a * b) *n cN)    ≡⟨ cong (fromℕ ∘ (_*n cN)) (toℕ*homo a b) ⟩
    fromℕ ((aN *n bN) *n cN)     ≡⟨ cong fromℕ (*n-assoc aN bN cN) ⟩
    fromℕ (aN *n (bN *n cN))     ≡⟨ cong (fromℕ ∘ (aN *n_))
                                                  (sym (toℕ*homo b c)) ⟩
    fromℕ (aN *n toℕ (b * c))    ≡⟨ cong fromℕ (sym (toℕ*homo a (b * c))) ⟩
    fromℕ (toℕ (a * (b * c)))    ≡⟨ fromℕ∘toℕ (a * (b * c)) ⟩
    (a * (b * c))
  ∎
  where
  aN = toℕ a;   bN = toℕ b;   cN = toℕ c

---------------------------
*2≗*2bin :  _*2 ≗ (_* 2')
*2≗*2bin x =
           begin x *2      ≡⟨ *2≗2bin* x ⟩
                 2' * x    ≡⟨ *-comm 2' x ⟩
                 x * 2'
           ∎

lDistrib :  FP-Bin._DistributesOverˡ_ _*_  _+_
lDistrib a b c = 
  begin 
    a * (b + c)                         ≡⟨ sym (fromℕ∘toℕ (a * (b + c))) ⟩
    fromℕ (toℕ (a * (b + c)))           ≡⟨ cong fromℕ (toℕ*homo a (b + c)) ⟩
    fromℕ (aN *n (toℕ (b + c)))         ≡⟨ cong (fromℕ ∘ (aN *n_)) 
                                                         (toℕ+homo b c) ⟩
    fromℕ (aN *n (bN +n cN))            ≡⟨ cong fromℕ (*n-lDistrib aN bN cN) ⟩
    fromℕ (aN *n bN +n aN *n cN)        ≡⟨ cong fromℕ 
                                           (cong₂ _+n_ (sym (toℕ*homo a b))
                                                       (sym (toℕ*homo a c)))
                                         ⟩
    fromℕ (toℕ (a * b) +n toℕ (a * c))  ≡⟨ cong fromℕ 
                                              (sym (toℕ+homo (a * b) (a * c))) 
                                         ⟩
    fromℕ (toℕ (a * b + a * c))         ≡⟨ fromℕ∘toℕ (a * b + a * c) ⟩
    a * b + a * c
  ∎
  where
  aN = toℕ a;   bN = toℕ b;   cN = toℕ c


rDistrib :  FP-Bin._DistributesOverʳ_ _*_ _+_
rDistrib a b c = 
  begin 
    (b + c) * a                         ≡⟨ sym (fromℕ∘toℕ ((b + c) * a)) ⟩
    fromℕ (toℕ ((b + c) * a))           ≡⟨ cong fromℕ (toℕ*homo (b + c) a) ⟩
    fromℕ ((toℕ (b + c)) *n aN)         ≡⟨ cong (fromℕ ∘ (_*n aN)) 
                                                         (toℕ+homo b c) ⟩
    fromℕ ((bN +n cN) *n aN)            ≡⟨ cong fromℕ (*n-rDistrib aN bN cN) ⟩
    fromℕ (bN *n aN +n cN *n aN)        ≡⟨ cong fromℕ 
                                           (cong₂ _+n_ (sym (toℕ*homo b a))
                                                       (sym (toℕ*homo c a)))
                                         ⟩
    fromℕ (toℕ (b * a) +n toℕ (c * a))  ≡⟨ cong fromℕ 
                                              (sym (toℕ+homo (b * a) (c * a))) 
                                         ⟩
    fromℕ (toℕ (b * a + c * a))         ≡⟨ fromℕ∘toℕ (b * a + c * a) ⟩
    b * a + c * a
  ∎
  where
  aN = toℕ a;   bN = toℕ b;   cN = toℕ c


distrib :  FP-Bin._DistributesOver_ _*_ _+_
distrib =  (lDistrib , rDistrib)

----------------------------------------------
*2-distrib :  ∀ a b → (a + b) *2 ≡ a *2 + b *2 
*2-distrib a b =
  begin 
    (a + b) *2         ≡⟨ *2≗*2bin (a + b) ⟩
    (a + b) * 2'       ≡⟨ rDistrib 2' a b ⟩
    a * 2' + b * 2'    ≡⟨ cong₂ _+_ (sym (*2≗*2bin a)) (sym (*2≗*2bin b)) ⟩
    a *2 + b *2    
  ∎              

*2≗+ :  ∀ x → x *2 ≡ x + x
*2≗+ x =  
       begin x *2               ≡⟨ *2≗*2bin x ⟩
             x * 2'             ≡⟨ refl ⟩
             x * (1' + 1')      ≡⟨ lDistrib x 1' 1' ⟩
             x * 1' + x * 1'    ≡⟨ cong₂ _+_ (*1 x) (*1 x) ⟩
             x + x
       ∎

-----------------------------------------------------
2^-homo :  (m n : ℕ) →  2^ (m +n n) ≡ (2^ m) * (2^ n)
2^-homo 0      _ =  refl
2^-homo (1+ m) n =
        begin
          2^ ((1+ m) +n n)       ≡⟨ cong 2^_ (sym (+n-assoc 1 m n)) ⟩
          2^ (1+ (m +n n))       ≡⟨ 2^suc (m +n n) ⟩
          (2^ (m +n n)) *2       ≡⟨ cong _*2 (2^-homo m n) ⟩
          (2^ m * 2^ n) *2       ≡⟨ sym (*2-assoc (2^ m) (2^ n)) ⟩
          ((2^ m) *2) * (2^ n)   ≡⟨ cong (_* (2^ n)) (sym (2^suc m)) ⟩
          (2^ (1+ m)) * (2^ n)
        ∎

------------------------------------------------------------------------------
toℕ-2^-homo :  toℕ ∘ 2^_ ≗ (2 ^n_)

toℕ-2^-homo 0      =  refl
toℕ-2^-homo (1+ n) =
             begin toℕ (2^ (1+ n))       ≡⟨ cong toℕ (2^suc n) ⟩
                   toℕ ((2^ n) *2)       ≡⟨ cong toℕ (*2≗*2bin (2^ n)) ⟩
                   toℕ ((2^ n) * 2')     ≡⟨ toℕ*homo (2^ n) 2' ⟩
                   toℕ (2^ n) *n 2       ≡⟨ cong (_*n 2) (toℕ-2^-homo n) ⟩
                   (2 ^n n) *n 2         ≡⟨ refl ⟩
                   (2 ^n n) *n (2 ^n 1)  ≡⟨ sym (NProp.^-distribˡ-+-* 2 n 1) ⟩
                   2 ^n (n +n 1)         ≡⟨ cong (2 ^n_) (+n-comm n 1) ⟩
                   2 ^n (1+ n)
             ∎

-----------------------------------------------
shift-e≗2^e* :  (e : ℕ) → shift e ≗ ((2^ e) *_)
shift-e≗2^e* 0      _  =  refl
shift-e≗2^e* (1+ e) 0# =  begin shift (1+ e) 0#     ≡⟨ refl ⟩
                                0#                  ≡⟨ sym (*0 (2^ (1+ e))) ⟩
                                (2^ (1+ e)) * 0#
                          ∎
shift-e≗2^e* (1+ e) (bs 1#) =  
        begin 
          shift (1+ e) (bs 1#)       ≡⟨ refl ⟩
          shift e ((0b ∷ bs) 1#)     ≡⟨ shift-e≗2^e* e ((0b ∷ bs) 1#) ⟩
          (2^ e) * ((0b ∷ bs) 1#)    ≡⟨ cong ((2^ e) *_) (*2≗2bin* bs1) ⟩
          (2^ e) * (2' * bs1)        ≡⟨ sym (*-assoc (2^ e) 2' bs1) ⟩
          ((2^ e) * 2') * bs1        ≡⟨ cong (_* bs1) 
                                             (sym (shift-e≗2^e* e 2')) ⟩
          (shift e 2') * bs1         ≡⟨ refl ⟩
          (shift (1+ e) 1') * bs1    ≡⟨ refl ⟩
          (2^ (1+ e)) * bs1
        ∎
        where bs1 = bs 1#

------------------------------------------------------------------------------
partHighest-2^  :  ∀ bs → bs 1# ≡ (fromBits bs) + 2^ (ln bs)
partHighest-2^ []        =  refl
partHighest-2^ (⊥b ∷ _)
partHighest-2^ (0b ∷ bs) = 
    begin
      (0b ∷ bs) 1#                    ≡⟨ refl ⟩
      (bs 1#) *2                      ≡⟨ cong _*2 (partHighest-2^ bs) ⟩
      (<bs> + (2^ (ln bs))) *2        ≡⟨ *2-distrib <bs> (2^ (ln bs)) ⟩
      <bs> *2 + (2^ (ln bs)) *2       ≡⟨ cong ((<bs> *2) +_) 
                                                       (sym (2^suc (ln bs))) ⟩
      <bs> *2 + 2^1+|bs|              ≡⟨ cong (_+ 2^1+|bs|)
                                              (sym (fromBits-0:bs-as*2 bs)) ⟩
      (fromBits (0b ∷ bs)) + 2^1+|bs|
    ∎
    where
    <bs> = fromBits bs;   2^1+|bs| = 2^ (1+ ln bs)

partHighest-2^ (1b ∷ bs) = 
  begin 
    (1b ∷ bs) 1#                     ≡⟨ sym (suc-even1 bs) ⟩
    1' + (bs 1#) *2                ≡⟨ cong (suc ∘ _*2) (partHighest-2^ bs) ⟩
    1' + (<bs> + (2^ (ln bs))) *2      ≡⟨ cong suc 
                                              (*2-distrib <bs> (2^ (ln bs))) ⟩
    1' + (<bs> *2 + (2^ (ln bs)) *2)   ≡⟨ cong (suc ∘ ((<bs> *2) +_)) 
                                                       (sym (2^suc (ln bs))) ⟩ 
    1' + (<bs> *2  + 2^1+|bs|)    ≡⟨ sym (+-assoc 1' (<bs> *2) 2^1+|bs|) ⟩ 
    (suc (<bs> *2)) + 2^1+|bs|      ≡⟨ cong (_+ 2^1+|bs|) 
                                           (sym (fromBits-1:bs-as-suc*2 bs)) ⟩
    (fromBits (1b ∷ bs)) + 2^1+|bs|
  ∎
  where
  <bs> = fromBits bs;   2^1+|bs| = 2^ (1+ ln bs)

------------------------------------------------------------------------------
-- The goal is to prove that   pred (2^ (1+ n))  has order  1+ n.
-- In particular, subtracting a nonzero from  2^ (1+ n)  decreases the order. 

toBits-pred-2^[1+n]-eq :  ∀ n → 
                            toBits (pred (2^ (1+ n))) ≡ (replicate n 1b) ∷ʳ 1b
toBits-pred-2^[1+n]-eq n =  
  begin
    toBits (pred (2^ n'))                          ≡⟨ refl ⟩
    toBits (fromBits (predList (toBits (2^ n'))))  
                                 ≡⟨ cong (to ∘ from ∘ predList) (toBits-2^ n') 
                                  ⟩
    toBits (fromBits (predList ((replicate n' 0b) ∷ʳ 1b)))  
                                    ≡⟨ cong (to ∘ from) (predList[repl-0]:1 n) 
                                     ⟩
    toBits (fromBits ((replicate n 1b) ∷ʳ 1b))  
                                ≡⟨ toBits∘fromBits (units ∷ʳ 1b) hl1-units:1 ⟩
    (replicate n 1b) ∷ʳ 1b  
  ∎
  where
  n' = 1+ n;  to = toBits;  from = fromBits;  units = replicate n 1b

  hl1-units:1 = hasLast1-bs:1 units


|pred-2^[1+n]|≡1+n :  ∀ n → ∣ pred (2^ (1+ n)) ∣ ≡ 1+ n
|pred-2^[1+n]|≡1+n n =  
  begin 
    ∣ pred (2^ n') ∣             ≡⟨ refl ⟩
    ln (toBits (pred (2^ n')))   ≡⟨ cong ln (toBits-pred-2^[1+n]-eq n) ⟩
    ln ((replicate n 1b) ∷ʳ 1b)  ≡⟨ length-xs:x 1b (replicate n 1b) ⟩
    1+ ln (replicate n 1b)       ≡⟨ cong 1+_ (length-replicate n) ⟩
    1+ n
  ∎ 
  where  n' = 1+ n

|pred-2^[1+n]|<|2^[1+n]| :  ∀ n → ∣ pred (2^ (1+ n)) ∣ <n ∣ 2^ (1+ n) ∣
|pred-2^[1+n]|<|2^[1+n]| n = 
             ≤n-reflexive $
             begin 
               1+ ∣ pred (2^ (1+ n)) ∣   ≡⟨ cong 1+_ (|pred-2^[1+n]|≡1+n n) ⟩
               2 +n n                    ≡⟨ sym (|2^n|≡1+n (1+ n)) ⟩
               ∣ 2^ (1+ n) ∣
             ∎

------------------------------------------------------------------------------
-- These are about the division relation.

∣x⇒∣y*x :  {x : Bin} → (y z : Bin) → x ∣ y → x ∣ z * y
∣x⇒∣y*x {x} y z (q , xq≡y) =
                           (z * q , xzq≡zy)
                where
                xzq≡zy :  x * (z * q) ≡ z * y
                xzq≡zy =  begin x * (z * q)   ≡⟨ sym (*-assoc x z q) ⟩
                                (x * z) * q   ≡⟨ cong (_* q) (*-comm x z) ⟩
                                (z * x) * q   ≡⟨ *-assoc z x q ⟩
                                z * (x * q)   ≡⟨ cong (z *_) xq≡y ⟩
                                z * y
                          ∎

∣+ :  ∀ {x} → (y z : Bin) → x ∣ y → x ∣ z → x ∣ (y + z)
∣+ {x} y z (q , xq≡y) (q' , xq'≡z) =
                                   (q + q' , x[q+q']≡y+z)
           where
           x[q+q']≡y+z = begin x * (q + q')     ≡⟨ lDistrib x q q' ⟩
                               x * q + x * q'   ≡⟨ cong₂ _+_ xq≡y xq'≡z ⟩
                               y + z
                         ∎


