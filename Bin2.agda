{-                                                            
This file is a part of the library  Binary-3.2.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.  

Binary-3.1  is free software: you can redistribute it and/or modify it 
under the terms of the GNU General Public License.
See  license.txt.
-}

module Bin2 where

open import Level    using () renaming (zero to 0ℓ) 
open import Function using (id; const; _∘_; _$_; case_of_) 
import Algebra.FunctionProperties as FuncProp
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Unary   using (Decidable; _⊆_)
open import Relation.Binary  using (Rel; DecSetoid)
                             renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality as PE using 
                         (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; _≗_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_; [_]; _∷ʳ_; map; replicate)
                      renaming (length to ln)
open import Data.List.Properties as ListProp using (map-compose; map-cong)
open import Data.List.All   using (All) renaming ([] to []a; _∷_ to _∷a_)
import Data.List.All.Properties as AllProp
open import Data.List.Any using (Any)
import Data.List.Membership.Setoid as Membership
open import Data.Fin as Fin using (Fin; zero) renaming (suc to 1+_)
open import Data.Fin.Properties as FinP using (prop-toℕ-≤)
open import Data.Digit      using (Bit; fromDigits)
open import Data.Nat as Nat using (ℕ; zero; z≤n; s≤s; _∸_)
            renaming (suc to 1+_; pred to predN; _<_ to _<n_; _>_ to _>n_; 
                      _≤_ to _≤n_; _+_ to _+n_; _*_ to _*n_; _≟_ to _≟n_
                     )
open import Data.Nat.Properties as NatP using
          (≤-refl; ≤-trans; ≤-antisym; <⇒≢; m+n∸n≡m; *-identityˡ; m≤m+n; 
           _*-mono_; *-mono-≤; ⌊n/2⌋-mono; module ≤-Reasoning
          )
          renaming (+-comm to +n-comm; +-assoc to +n-assoc; *-comm to *n-comm)

open import Data.Nat.DivMod as DM using (_divMod_; _div_)
open PE.≡-Reasoning
open ≤-Reasoning using () renaming (begin_ to ≤begin_; _∎ to _≤end;
                                    _≡⟨_⟩_ to _≡≤[_]_; _≤⟨_⟩_ to _≤[_]_
                                   )
open import Algebra using (Monoid)

-- of application ---
open import List0 using (tail0; all-map-const; all-xs=c→map-c-xs≡xs; Null; 
                         null?; null⇒≡[]; map-replicate; all≡in-replicate;
                         replicate-m+n; Search; search; found′
                        ) 
open import NatProp0 using (>⇒≢; ≤0⇒≡0; Even; *1; half; 0<1+n; half<n*2>; 
                            half-suc-n≤n; odd-suc; even-2*
                           )
open import NatDivMod using (half-n=n-div-2)
open import Bin0 using 
     (Bin; Bin⁺; _≡b_; _≢b_; const-0b; const-1b; toBits; fromBits; 
      fromBits-aux; toℕ; addBits; addBL; addBL-aux; addCarry; suc; _*2; 
      predList; minusCarry; minusCarry-aux; pred; _+_; _<_; _≟b_
     )
     renaming (1bin to 1') 

open import Bin1 using (≢sym; ≟0b; ≟1b; 0b≢1b; 1b≢0b; ≢0b⇒≡1b; ≢1b⇒≡0b; _≟_;
                                        <-irrefl; cutTrailing-0b; ∣_∣; bs1≢0)



--****************************************************************************
-- 0 <--> [],  and a binary code either is  []  or ends with  1b
--                                                        (as the higher bit).
-- This higher bit condition is expressed below as  HasLast1if, HasLast1.
--
-- It is proved below that   ℕ  <--suc-isomorphic-->  Bin⁺ ∩ HasLast1if.

-- This module provides proofs for statements about  sum of binary numbers.


open Bin

pattern 0b = zero
pattern 1b = 1+ zero
pattern ⊥b = 1+ 1+ ()

const1∘const0 :  const-1b ∘ const-0b ≗ const-1b
const1∘const0 _ =  refl

const0∘const1 :  const-0b ∘ const-1b ≗ const-0b
const0∘const1 _ =  refl

addC1 = addCarry 1b


------------------------------------------------------------------------------
-- Below it is widely used that  (a : Bin) ≢ 0#  iff  HasLast1 (toBits a)
--                               iff  (toBits a) has form  (bs ++ [ 1b ])
--                                               (which is also (bs ∷ʳ 1b)).  

fromBits-bs:1 :  fromBits ∘ (_∷ʳ 1b) ≗ _1#

fromBits-bs:1 []       =  refl
fromBits-bs:1 (b ∷ bs) = 
  begin
    fromBits ((b ∷ bs) ∷ʳ 1b)               ≡⟨ refl ⟩
    fromBits (b ∷ (bs ∷ʳ 1b))               ≡⟨ refl ⟩
    fromBits-aux b (fromBits (bs ∷ʳ 1b))    ≡⟨ cong (fromBits-aux b)
                                                    (fromBits-bs:1 bs) ⟩ 
    fromBits-aux b (bs 1#)                  ≡⟨ refl ⟩
    (b ∷ bs) 1# 
  ∎


-- Several lemmata for  HasLast1(if) -----------------------------------------

HasLast1 : List Bit → Set
HasLast1 []           = ⊥
HasLast1 (b ∷ [])     = b ≡ 1b
HasLast1 (_ ∷ b ∷ bs) = HasLast1 (b ∷ bs)

hasLast1-cons :  (b : Bit) → (bs : List Bit) → HasLast1 bs → HasLast1 (b ∷ bs)

hasLast1-cons _ (b' ∷ bs) hl1-b':bs =  hl1-b':bs
hasLast1-cons _ []        ()


hasLast1-++ :  (bs bs' : List Bit) → HasLast1 bs' → HasLast1 (bs ++ bs')
hasLast1-++ []       bs' hl1-bs' =  hl1-bs'
hasLast1-++ (b ∷ bs) bs' hl1-bs' =  hasLast1-cons b (bs ++ bs')
                                             (hasLast1-++ bs bs' hl1-bs')

hasLast1-bs:1 :  (bs : List Bit) → HasLast1 (bs ∷ʳ 1b)
hasLast1-bs:1 bs =  
                 hasLast1-++ bs [ 1b ] refl 

bs=1→hasLast1-1bs :  ∀ bs → All (_≡ 1b) bs → HasLast1 (1b ∷ bs)

bs=1→hasLast1-1bs []        _            =  refl
bs=1→hasLast1-1bs (⊥b ∷ _) 
bs=1→hasLast1-1bs (0b ∷ _)  (0b≡1b ∷a _) =  ⊥-elim (0b≢1b 0b≡1b)
bs=1→hasLast1-1bs (1b ∷ bs) (_ ∷a bs=1)  =  
                                         hasLast1-cons 1b (1b ∷ bs) hl1-1:bs
                                         where
                                         hl1-1:bs = bs=1→hasLast1-1bs bs bs=1

hasLast1→is++1b :  (bs : List Bit) → HasLast1 bs → (∃ \bs' → bs ≡ bs' ∷ʳ 1b)
hasLast1→is++1b []            () 
hasLast1→is++1b (1b ∷ [])     _        =  ([] , refl)
hasLast1→is++1b (0b ∷ [])     () 
hasLast1→is++1b (⊥b ∷ _)
hasLast1→is++1b (b ∷ b' ∷ bs) hl1-b'bs =
                let
                  (bs' , b'bs≡bs':1) = hasLast1→is++1b (b' ∷ bs) hl1-b'bs 

                  eq :  b ∷ b' ∷ bs ≡ (b ∷ bs') ∷ʳ 1b
                  eq =  cong (b ∷_) b'bs≡bs':1  
                in
                (b ∷ bs' , eq)

HasLast1if : List Bit → Set              -- "empty or ends with 1b"
HasLast1if []           =  ⊤
HasLast1if (b ∷ [])     =  b ≡ 1b
HasLast1if (_ ∷ b ∷ bs) =  HasLast1if (b ∷ bs)

hasLast1→hasLast1if : ∀ bs → HasLast1 bs → HasLast1if bs
hasLast1→hasLast1if []           ()
hasLast1→hasLast1if (_ ∷ [])     hl1      = hl1
hasLast1→hasLast1if (_ ∷ b ∷ bs) hl1-b-bs =
                                       hasLast1→hasLast1if (b ∷ bs) hl1-b-bs

hasLast1if→hasLast1 : ∀ b bs → HasLast1if (b ∷ bs) → HasLast1 (b ∷ bs)
hasLast1if→hasLast1 _ []            hl =  hl
hasLast1if→hasLast1 _ (_ ∷ [])      hl =  hl
hasLast1if→hasLast1 b (_ ∷ b' ∷ bs) hl =  hasLast1if→hasLast1 b (b' ∷ bs) hl

hasLast1if-tail0 : (bs : Bin⁺) → HasLast1if bs → HasLast1if (tail0 bs)
hasLast1if-tail0 []          _ = ⊤.tt
hasLast1if-tail0 (_ ∷ [])    _ = ⊤.tt
hasLast1if-tail0 (_ ∷ _ ∷ _) p = p

hasLast1∘toBits :  {a : Bin} → a ≢ 0# → HasLast1 (toBits a)

hasLast1∘toBits {0#}    0≢0 =  ⊥-elim (0≢0 refl)
hasLast1∘toBits {bs 1#} _   =  hasLast1-bs:1 bs
                                               
------------------------------------------------------------------------------
toBits∘fromBits :  ∀ bs → HasLast1 bs → toBits (fromBits bs) ≡ bs

toBits∘fromBits bs hl1-bs = 
  let
    (bs' , bs≡bs':1) = hasLast1→is++1b bs hl1-bs 
  in
  begin
    toBits (fromBits bs)            ≡⟨ cong (toBits ∘ fromBits) bs≡bs':1 ⟩
    toBits (fromBits (bs' ∷ʳ 1b))   ≡⟨ cong toBits (fromBits-bs:1 bs') ⟩
    toBits (bs' 1#)                 ≡⟨ refl ⟩
    bs' ∷ʳ 1b                       ≡⟨ sym bs≡bs':1 ⟩ 
    bs 
  ∎

------------------------------------------------------------------------------
hasLast1-addC1 : (bs : List Bit) → HasLast1if bs → HasLast1 (addC1 bs)
hasLast1-addC1 []         _  = refl
hasLast1-addC1 (1b ∷ [])  _  = refl
hasLast1-addC1 (0b  ∷ []) ()
hasLast1-addC1 (⊥b ∷ _)
hasLast1-addC1 (0b ∷ b ∷ bs) hl1if-0:b:bs =
                                          hasLast1if→hasLast1 b bs hl1if-b:bs
               where
               hl1if-b:bs = hasLast1if-tail0 (zero ∷ b ∷ bs) hl1if-0:b:bs

hasLast1-addC1 (1b ∷ b:bs) hl1if-1:b:bs =  hl1-0:addC1-b:bs
         where
         hl1if-b:bs     = hasLast1if-tail0 (1b ∷ b:bs) hl1if-1:b:bs
         addC1-b:bs     = addC1 b:bs
         hl1-addC1-b:bs = hasLast1-addC1 (b:bs) hl1if-b:bs   -- recursion

         hl1-0:addC1-b:bs : HasLast1 (zero ∷ addC1-b:bs)
         hl1-0:addC1-b:bs = hasLast1-cons zero addC1-b:bs hl1-addC1-b:bs

---------------------------------------------------------------------
hasLast1<addC1-bs:1> :  (bs : List Bit) → HasLast1 (addC1 (bs ∷ʳ 1b)) 
hasLast1<addC1-bs:1> bs =  
                        hasLast1-addC1 (bs ∷ʳ 1b) hl1if-bs1
               where
               hl1if-bs1 = hasLast1→hasLast1if (bs ∷ʳ 1b) (hasLast1-bs:1 bs)

-----------------------------------------
fromBits∘toBits :  fromBits ∘ toBits ≗ id
fromBits∘toBits 0#      =  refl
fromBits∘toBits (bs 1#) =  fromBits-bs:1 bs 

addBL-0-bs-[] :  ∀ bs → addBL 0b bs [] ≡ bs
addBL-0-bs-[] []      = refl
addBL-0-bs-[] (_ ∷ _) = refl

addBL-1-bs-[] :  ∀ bs → addBL 1b bs [] ≡ addC1 bs
addBL-1-bs-[] []      =  refl
addBL-1-bs-[] (_ ∷ _) =  refl

------------------------------------------------------------------------------
addBL-1-as-addC1 : ∀ bs bs' → addBL 1b bs bs' ≡ addC1 (addBL 0b bs bs')

addBL-1-as-addC1 [] _  =  refl 
addBL-1-as-addC1 bs [] =  
            begin 
              addBL 1b bs []          ≡⟨ addBL-1-bs-[] bs ⟩
              addC1 bs                ≡⟨ cong addC1 (sym $ addBL-0-bs-[] bs) ⟩
              addC1 (addBL 0b bs [])
            ∎
addBL-1-as-addC1 (⊥b ∷ _) 
addBL-1-as-addC1 _         (⊥b ∷ _) 
addBL-1-as-addC1 (0b ∷ bs) (0b ∷ bs') =  refl
addBL-1-as-addC1 (0b ∷ bs) (1b ∷ bs') =  
  begin
    addBL 1b (0b ∷ bs) (1b ∷ bs')          ≡⟨ refl ⟩
    0b ∷ (addBL 1b bs bs')                 ≡⟨ cong (0b ∷_) 
                                             (addBL-1-as-addC1 bs bs') ⟩
    0b ∷ (addC1 (addBL 0b bs bs'))         ≡⟨ refl ⟩
    addC1 (addBL 0b (0b ∷ bs) (1b ∷ bs'))
  ∎
addBL-1-as-addC1 (1b ∷ bs) (0b ∷ bs') = cong (0b ∷_) (addBL-1-as-addC1 bs bs')
addBL-1-as-addC1 (1b ∷ bs) (1b ∷ bs') = refl 

--------------------------------------------------
[1b]+ :  ∀ bs → addBL 0b [ 1b ] bs ≡ addC1 bs
[1b]+ []       = refl
[1b]+ (0b ∷ _) = refl
[1b]+ (1b ∷ _) = refl
[1b]+ (⊥b ∷ _)

+[1b] :  ∀ bs → addBL 0b bs [ 1b ] ≡ addC1 bs
+[1b] []        =  refl
+[1b] (⊥b ∷ _)
+[1b] (0b ∷ bs) =  cong (1b ∷_) (addBL-0-bs-[] bs)
+[1b] (1b ∷ bs) = 
  begin 
    addBL 0b (1b ∷ bs) (1b ∷ [])    ≡⟨ refl ⟩  
    0b ∷ (addBL 1b bs [])           ≡⟨ cong (0b ∷_) (addBL-1-as-addC1 bs []) ⟩
    0b ∷ (addC1 (addBL 0b bs []))      
                                ≡⟨ cong ((0b ∷_) ∘ addC1) (addBL-0-bs-[] bs) ⟩
    0b ∷ (addC1 bs)     
  ∎

suc-even1 :  ∀ bs → suc ((0b ∷ bs) 1#) ≡ (1b ∷ bs) 1#
suc-even1 bs =                                                             
    begin 
      1' + ((0b ∷ bs) 1#)                              ≡⟨ refl ⟩
      fromBits (addBL 0b [ 1b ] ((0b ∷ bs) ∷ʳ 1b)) 
                                           ≡⟨ cong fromBits 
                                                   ([1b]+ ((0b ∷ bs) ∷ʳ 1b)) ⟩
      fromBits (addC1 ((0b ∷ bs) ∷ʳ 1b))   ≡⟨ refl ⟩
      fromBits ((1b ∷ bs) ∷ʳ 1b)           ≡⟨ fromBits-bs:1 (1b ∷ bs) ⟩
      (1b ∷ bs) 1#                                                          
    ∎

------------------------------------------------------------------------------
fromBits-1:bs-as-suc*2 :  ∀ bs → fromBits (1b ∷ bs) ≡ suc ((fromBits bs) *2)
fromBits-1:bs-as-suc*2 bs =
                          aux <bs> refl 
  where
  <bs> = fromBits bs

  aux :  (x : Bin) → x ≡ <bs> →  fromBits (1b ∷ bs) ≡  suc ((fromBits bs) *2)
  aux 0# 0≡<bs> =
         begin fromBits (1b ∷ bs)    ≡⟨ refl ⟩
               fromBits-aux 1b <bs>  ≡⟨ cong (fromBits-aux 1b) (sym 0≡<bs>) ⟩
               fromBits-aux 1b 0#    ≡⟨ refl ⟩
               1'                    ≡⟨ refl ⟩
               suc (0# *2)           ≡⟨ cong (suc ∘ _*2) 0≡<bs> ⟩
               suc (<bs> *2)
         ∎

  aux (bs' 1#) bs'1≡<bs> =
      begin
        fromBits (1b ∷ bs)         ≡⟨ refl ⟩
        fromBits-aux 1b <bs>       ≡⟨ cong (fromBits-aux 1b) (sym bs'1≡<bs>) ⟩
        fromBits-aux 1b (bs' 1#)   ≡⟨ refl ⟩
        (1b ∷ bs') 1#              ≡⟨ sym (suc-even1 bs') ⟩
        suc ((bs' 1#) *2)          ≡⟨ cong (suc ∘ _*2) bs'1≡<bs> ⟩
        suc (<bs> *2)
      ∎

-----------------------------------------------------------------------------
bs:1+bs:1-asShift :  ∀ bs → addBL 0b (bs ∷ʳ 1b) (bs ∷ʳ 1b) ≡ 0b ∷ (bs ∷ʳ 1b)
bs:1+bs:1-asShift []        =  refl
bs:1+bs:1-asShift (⊥b ∷ _)
bs:1+bs:1-asShift (0b ∷ bs) =  cong (0b ∷_) (bs:1+bs:1-asShift bs) 
bs:1+bs:1-asShift (1b ∷ bs) = 
  begin
    addBL 0b (1b ∷ (bs ∷ʳ 1b)) (1b ∷ (bs ∷ʳ 1b))        ≡⟨ refl ⟩
    addBL-aux (bs ∷ʳ 1b) (bs ∷ʳ 1b) (1b , 0b)           ≡⟨ refl ⟩
    0b ∷ (addBL 1b (bs ∷ʳ 1b) (bs ∷ʳ 1b))
                      ≡⟨ cong (0b ∷_) (addBL-1-as-addC1 (bs ∷ʳ 1b) (bs ∷ʳ 1b))
                       ⟩
    0b ∷ (addC1 (addBL 0b (bs ∷ʳ 1b) (bs ∷ʳ 1b)))
                              ≡⟨ cong ((0b ∷_) ∘ addC1) (bs:1+bs:1-asShift bs) 
                               ⟩ 
    0b ∷ (addC1 (0b ∷ (bs ∷ʳ 1b)))   ≡⟨ refl ⟩
    0b ∷ (1b ∷ (bs ∷ʳ 1b))
  ∎

x1#+x1#-asShift :  ∀ bs → (bs 1#) + (bs 1#) ≡ (0b ∷ bs) 1#
x1#+x1#-asShift bs =
    begin
      fromBits (addBL 0b (bs ∷ʳ 1b) (bs ∷ʳ 1b))   ≡⟨ cong fromBits 
                                                      (bs:1+bs:1-asShift bs) ⟩
      fromBits (0b ∷ (bs ∷ʳ 1b))                  ≡⟨ fromBits-bs:1 (0b ∷ bs) ⟩
      (0b ∷ bs) 1#
    ∎


-----------------------------------------------
suc-as-addC1 :  suc ≗ fromBits ∘ addC1 ∘ toBits 
suc-as-addC1 = 
              cong fromBits ∘ [1b]+ ∘ toBits 

----------------------------------------------
toBits∘suc-eq :  toBits ∘ suc ≗ addC1 ∘ toBits 

toBits∘suc-eq 0#      =  refl
toBits∘suc-eq (bs 1#) =  
  begin 
    toBits (suc (bs 1#))            ≡⟨ cong toBits (suc-as-addC1 (bs 1#)) ⟩
    toBits (fromBits (addC1 bs1))   ≡⟨ toBits∘fromBits (addC1 bs1) hl1-1+bs1 ⟩ 
    addC1 bs1  
  ∎
  where
  bs1       = bs ∷ʳ 1b
  hl1-1+bs1 = hasLast1<addC1-bs:1> bs


addBits-00 :  ∀ b → addBits 0b 0b b ≡ (0b , b)
addBits-00 0b = refl
addBits-00 1b = refl
addBits-00 ⊥b

addBits-0b0 :  ∀ b → addBits 0b b 0b ≡ (0b , b)
addBits-0b0 0b = refl
addBits-0b0 1b = refl
addBits-0b0 ⊥b


-------------------
0+ :  (0# +_) ≗ id

0+ 0#            =  refl
0+ ([] 1#)       =  refl
0+ ((b ∷ bs) 1#) = 
  begin 
    0# + ((b ∷ bs) 1#)                                          ≡⟨ refl ⟩
    fromBits (addBL 0b (0b ∷ []) (b ∷ (bs ∷ʳ 1b)))              ≡⟨ refl ⟩
    fromBits (addBL-aux [] (bs ∷ʳ 1b) (addBits 0b 0b b))
                                         ≡⟨ cong (fromBits ∘ addBL-aux [] bs') 
                                                 (addBits-00 b)
                                          ⟩
    fromBits (addBL-aux [] (bs ∷ʳ 1b) (0b , b))   ≡⟨ refl ⟩
    fromBits (b ∷ (addBL 0b [] (bs ∷ʳ 1b)))       ≡⟨ refl ⟩
    fromBits (b ∷ (addCarry 0b (bs ∷ʳ 1b)))       ≡⟨ refl ⟩
    fromBits (b ∷ (bs ∷ʳ 1b))                     ≡⟨ refl ⟩
    fromBits-aux b (fromBits (bs ∷ʳ 1b))          ≡⟨ cong (fromBits-aux b) 
                                                          (fromBits-bs:1 bs) ⟩
    fromBits-aux b (bs 1#)                        ≡⟨ refl ⟩
    (b ∷ bs) 1#
  ∎ 
  where bs' = bs ∷ʳ 1b

-------------------
+0 :  (_+ 0#) ≗ id

+0 0#            =  refl
+0 ([] 1#)       =  refl
+0 ((b ∷ bs) 1#) =  
  begin 
    ((b ∷ bs) 1#) + 0#                                    ≡⟨ refl ⟩
    fromBits (addBL 0b (b ∷ bs') (0b ∷ []))               ≡⟨ refl ⟩
    fromBits (addBL-aux bs' [] (addBits 0b b 0b))
                                         ≡⟨ cong (fromBits ∘ addBL-aux bs' []) 
                                                 (addBits-0b0 b)
                                          ⟩
    fromBits (addBL-aux bs' [] (0b , b))     ≡⟨ refl ⟩
    fromBits (b ∷ (addBL 0b bs' []))         ≡⟨ cong (fromBits ∘ (b ∷_)) 
                                                     (addBL-0-bs-[] bs') ⟩
    fromBits (b ∷ (bs ∷ʳ 1b))                ≡⟨ refl ⟩
    fromBits-aux b (fromBits (bs ∷ʳ 1b))     ≡⟨ cong (fromBits-aux b) 
                                                     (fromBits-bs:1 bs) ⟩
    fromBits-aux b (bs 1#)                   ≡⟨ refl ⟩
    (b ∷ bs) 1#
  ∎
  where  bs' = bs ∷ʳ 1b


------------------------------------------------------------------------------
addC1-assoc :  (bs bs' : List Bit) → addBL 0b (addC1 bs) bs' ≡
                                     addC1 (addBL 0b bs bs') 
addC1-assoc [] bs' =  [1b]+ bs'
addC1-assoc bs []  =  
   begin
     addBL 0b (addC1 bs) []    ≡⟨ addBL-0-bs-[] (addC1 bs) ⟩
     addC1 bs                  ≡⟨ cong addC1 (sym $ addBL-0-bs-[] bs) ⟩
     addC1 (addBL 0b bs []) 
   ∎

addC1-assoc (⊥b ∷ _) 
addC1-assoc _         (⊥b ∷ _) 
addC1-assoc (0b ∷ bs) (0b ∷ bs') =  refl 
addC1-assoc (0b ∷ bs) (1b ∷ bs') =  cong (0b ∷_) (addBL-1-as-addC1 bs bs') 
addC1-assoc (1b ∷ bs) (0b ∷ bs') =  
  begin 
    addBL 0b (addC1 (1b ∷ bs)) (0b ∷ bs')   ≡⟨ refl ⟩
    0b ∷ (addBL 0b (addC1 bs) bs')          ≡⟨ cong (0b ∷_) 
                                                        (addC1-assoc bs bs') ⟩ 
    0b ∷ (addC1 (addBL 0b bs bs'))          ≡⟨ refl ⟩
    addC1 (addBL 0b (1b ∷ bs) (0b ∷ bs'))
  ∎

addC1-assoc (1b ∷ bs) (1b ∷ bs') = 
  begin
    addBL 0b (addC1 (1b ∷ bs)) (1b ∷ bs')     ≡⟨ refl ⟩
    1b ∷ (addBL 0b (addC1 bs) bs')   
                                        ≡⟨ cong (1b ∷_) (addC1-assoc bs bs') ⟩
    1b ∷ (addC1 (addBL 0b bs bs'))      ≡⟨ cong (1b ∷_) 
                                               (sym (addBL-1-as-addC1 bs bs'))
                                         ⟩
    1b ∷ (addBL 1b bs bs')                 ≡⟨ refl ⟩
    addC1 (addBL 0b (1b ∷ bs) (1b ∷ bs'))
  ∎


1:bs-1# :  ∀ bs → (1b ∷ bs) 1# ≡ 1' + (bs 1#) *2
1:bs-1# bs =   
           sym (fromBits-bs:1 (1b ∷ bs))

------------------------------------------------------------------------------
hasLast1<bs:1+bs':1> :  ∀ c bs bs' → HasLast1 (addBL c (bs ∷ʳ 1b) (bs' ∷ʳ 1b))
hasLast1<bs:1+bs':1> ⊥b 
hasLast1<bs:1+bs':1> _ (⊥b ∷ _) _
hasLast1<bs:1+bs':1> _ _        (⊥b ∷ _)

hasLast1<bs:1+bs':1> 0b [] bs' =  subst HasLast1 eq (hasLast1<addC1-bs:1> bs')
                         where
                        eq :  addC1 (bs' ∷ʳ 1b) ≡ addBL 0b [ 1b ] (bs' ∷ʳ 1b)
                        eq =  sym ([1b]+ (bs'  ∷ʳ 1b))

hasLast1<bs:1+bs':1> 0b bs [] =  subst HasLast1 eq (hasLast1<addC1-bs:1> bs)
                        where
                        eq :  addC1 (bs ∷ʳ 1b) ≡ addBL 0b (bs  ∷ʳ 1b) [ 1b ] 
                        eq =  sym (+[1b] (bs  ∷ʳ 1b))

hasLast1<bs:1+bs':1> 1b [] []         =  refl
hasLast1<bs:1+bs':1> 1b [] (0b ∷ bs') =  hasLast1-cons 0b (addC1 (bs' ∷ʳ 1b))
                                                          hl1-add1-bs':1 
                                    where
                                    hl1-add1-bs':1 =  hasLast1<addC1-bs:1> bs' 

hasLast1<bs:1+bs':1> 1b [] (1b ∷ [])      =  refl  
hasLast1<bs:1+bs':1> 1b [] (1b ∷ b ∷ bs') =  
                           hasLast1-cons 1b (addC1 ((b ∷ bs') ∷ʳ 1b)) hl1-tl
                           where
                           hl1-tl :  HasLast1 (addC1 ((b ∷ bs') ∷ʳ 1b))
                           hl1-tl =  hasLast1<addC1-bs:1> (b ∷ bs')

hasLast1<bs:1+bs':1> 1b (0b ∷ bs) [] =  subst HasLast1 (sym eq) hl1
   where
   eq :  addBL 1b ((0b ∷ bs) ∷ʳ 1b) (1b ∷ []) ≡ 0b ∷ (addC1 (bs ∷ʳ 1b))
   eq = 
      cong (0b ∷_) (addBL-1-bs-[] (bs ∷ʳ 1b))

   hl1-tail = hasLast1<addC1-bs:1> bs
   hl1      = hasLast1-cons 0b (addC1 (bs ∷ʳ 1b)) hl1-tail
  
  
hasLast1<bs:1+bs':1> 1b (1b ∷ bs) [] =  subst HasLast1 (sym eq) hl1
   where
   eq :  addBL 1b ((1b ∷ bs) ∷ʳ 1b) (1b ∷ []) ≡ 1b ∷ (addC1 (bs ∷ʳ 1b))
   eq = 
      cong (1b ∷_) (addBL-1-bs-[] (bs ∷ʳ 1b))

   hl1-tail = hasLast1<addC1-bs:1> bs
   hl1      = hasLast1-cons 1b (addC1 (bs ∷ʳ 1b)) hl1-tail

hasLast1<bs:1+bs':1> c (b ∷ bs) (b' ∷ bs') =  
  let
    (c' , b'') = addBits c b b'

    hl1-tl :  HasLast1 (addBL c' (bs ∷ʳ 1b) (bs' ∷ʳ 1b))
    hl1-tl =  hasLast1<bs:1+bs':1> c' bs bs' 
  in
  hasLast1-cons b'' (addBL c' (bs ∷ʳ 1b) (bs' ∷ʳ 1b)) hl1-tl

---------------------------------------------------------------
init-x1+y1 :  ∀ bs bs' → (∃ \bs'' → (bs 1# + bs' 1#) ≡ bs'' 1#)
init-x1+y1 bs bs' =                          -- sum of nonzeroes is nonzero
  let 
    listSum          = addBL 0b (bs ∷ʳ 1b) (bs' ∷ʳ 1b)
    hasLast1-listSum = hasLast1<bs:1+bs':1> 0b bs bs'

    (bs'' , bs'':1≡listSum) =  hasLast1→is++1b listSum hasLast1-listSum
 
    eq :  bs 1# + bs' 1# ≡ bs'' 1#
    eq =  
       begin bs 1# + bs' 1#                              ≡⟨ refl ⟩
             fromBits (addBL 0b (bs ∷ʳ 1b) (bs' ∷ʳ 1b))   
                                             ≡⟨ cong fromBits bs'':1≡listSum ⟩ 
             fromBits (bs'' ∷ʳ 1b)           ≡⟨ fromBits-bs:1 bs'' ⟩
             bs'' 1#
       ∎
  in
  (bs'' , eq)

------------------------------------------------------------------------------
suc-assoc :  ∀ a b → (suc a) + b ≡ suc (a + b)

suc-assoc 0# b  =  cong suc (sym (0+ b))
suc-assoc a  0# =  begin 
                     (suc a) + 0#    ≡⟨ +0 (suc a) ⟩
                     suc a           ≡⟨ cong suc (sym (+0 a)) ⟩
                     suc (a + 0#)
                   ∎

suc-assoc (bsA 1#) (bsB 1#) = 
  begin 
    (suc a) + b                                 ≡⟨ refl ⟩
    fromBits (addBL 0b (toBits (suc a)) bsB1)
                                     ≡⟨ cong (\x → fromBits (addBL 0b x bsB1))
                                             (toBits∘suc-eq a) 
                                      ⟩
    fromBits (addBL 0b (addC1 bsA1) bsB1)
                                     ≡⟨ cong fromBits (addC1-assoc bsA1 bsB1)
                                      ⟩
    fromBits (addC1 (addBL 0b bsA1 bsB1))
                        ≡⟨ cong (fromBits ∘ addC1) $ sym $ 
                           toBits∘fromBits (addBL 0b bsA1 bsB1) hl1-bsA1+bsB1
                         ⟩
    fromBits (addC1 (toBits (fromBits (addBL 0b bsA1 bsB1))))
                         ≡⟨ sym $ suc-as-addC1 (fromBits (addBL 0b bsA1 bsB1)) 
                          ⟩
    suc (fromBits (addBL 0b bsA1 bsB1))        ≡⟨ refl ⟩
    suc (a + b)
  ∎
  where
  a = bsA 1#;   b = bsB 1#;   bsA1 = bsA ∷ʳ 1b;   bsB1 = bsB ∷ʳ 1b

  hl1-bsA1+bsB1 :  HasLast1 (addBL 0b bsA1 bsB1)
  hl1-bsA1+bsB1 =  hasLast1<bs:1+bs':1> 0b bsA bsB 


------------------------------------------------------------------------------
addC1<units++0:bs> :
              (units bs : List Bit) → All (_≡ 1b) units →
              addC1 (units ++ (0b ∷ bs)) ≡ (map (const 0b) units) ++ (1b ∷ bs)

addC1<units++0:bs> []         _  _            =  refl
addC1<units++0:bs> (⊥b ∷ _) 
addC1<units++0:bs> (0b ∷ _)   _  (0b≡1b ∷a _) =  ⊥-elim (0b≢1b 0b≡1b)
addC1<units++0:bs> (1b ∷ uns) bs (_ ∷a uns=1) =   
                              cong (0b ∷_) (addC1<units++0:bs> uns bs uns=1)

------------------------------------------------------------------------------
minusCarry-aux∘++1 :  ∀ {bs} → minusCarry-aux (bs ∷ʳ 1b) ≡ 1b ∷ (bs ∷ʳ 1b)
minusCarry-aux∘++1 {[]}         = refl
minusCarry-aux∘++1 {⊥b ∷ _}
minusCarry-aux∘++1 {0b ∷ []}    = refl
minusCarry-aux∘++1 {0b ∷ _ ∷ _} = refl
minusCarry-aux∘++1 {1b ∷ _}     = refl


predList-01bs1 :  (bs : List Bit) → 
                  predList (0b ∷ 1b ∷ (bs ∷ʳ 1b)) ≡ 1b ∷ 0b ∷ (bs ∷ʳ 1b)

predList-01bs1 []      = refl
predList-01bs1 (_ ∷ _) = refl

-- predList (1b ∷ []) ≡ [ 0b ]   is by  refl

------------------------------------------------------------------------------
predList<0:zeroes:1> : 
                   ∀ zeroes → All (_≡ 0b) zeroes → 
                   predList ((0b ∷ zeroes) ∷ʳ 1b) ≡ 1b ∷ (map const-1b zeroes)

predList<0:zeroes:1> []         _            =  refl
predList<0:zeroes:1> (⊥b ∷ _)
predList<0:zeroes:1> (1b ∷ _)   (1b≡0b ∷a _) =  ⊥-elim (1b≢0b 1b≡0b)
predList<0:zeroes:1> (0b ∷ zrs) (_ ∷a zrs=0) =  
                         cong minusCarry-aux (predList<0:zeroes:1> zrs zrs=0) 

predList[repl-0]:1 :  ∀ n → predList ((replicate (1+ n) 0b) ∷ʳ 1b) ≡ 
                                     (replicate n 1b) ∷ʳ 1b
predList[repl-0]:1 n =
  begin
    predList ((replicate (1+ n) 0b) ∷ʳ 1b)  ≡⟨ refl ⟩
    predList (0b ∷ (zeroes ∷ʳ 1b))          ≡⟨ predList<0:zeroes:1> zeroes
                                                                    zeroes=0 ⟩
    1b ∷ (map const-1b zeroes)              ≡⟨ refl ⟩
    1b ∷ (map const-1b (replicate n 0b))    ≡⟨ cong (1b ∷_)
                                               (map-replicate const-1b n 0b) ⟩
    1b ∷ (replicate n 1b)        ≡⟨ refl ⟩
    replicate (1+ n) 1b          ≡⟨ cong (\k → replicate k 1b) (+n-comm 1 n) ⟩
    replicate (n +n 1) 1b        ≡⟨ replicate-m+n n 1 1b ⟩
    (replicate n 1b) ∷ʳ 1b
  ∎
  where
  zeroes   = replicate n 0b
  zeroes=0 = all≡in-replicate n 0b


------------------------------------------------------------------------------
predList<zeroes++<1:bs:1>> : (zeroes bs : List Bit) → All (_≡ 0b) zeroes → 
                             predList (zeroes ++ (1b ∷ (bs ∷ʳ 1b))) ≡ 
                                  (map const-1b zeroes) ++ (0b ∷ (bs ∷ʳ 1b))
 
predList<zeroes++<1:bs:1>> []             _  _            =  refl
predList<zeroes++<1:bs:1>> (⊥b ∷ _) 
predList<zeroes++<1:bs:1>> (0b ∷ [])      [] _            =  refl
predList<zeroes++<1:bs:1>> (_ ∷ ⊥b ∷ _) 
predList<zeroes++<1:bs:1>> (0b ∷ 0b ∷ zs) [] (_ ∷a 0zs=0) = 
                          cong minusCarry-aux 
                               (predList<zeroes++<1:bs:1>> (0b ∷ zs) [] 0zs=0)

predList<zeroes++<1:bs:1>> (1b ∷ _)     _ (1b≡0b ∷a _)      =  
                                                          ⊥-elim (1b≢0b 1b≡0b)
predList<zeroes++<1:bs:1>> (_ ∷ 1b ∷ _) _ (_ ∷a 1b≡0b ∷a _) = 
                                                          ⊥-elim (1b≢0b 1b≡0b)
predList<zeroes++<1:bs:1>> (0b ∷ []) (b ∷ bs) _ = 
                           cong minusCarry-aux 
                                (predList<zeroes++<1:bs:1>> [] (b ∷ bs) []a)

predList<zeroes++<1:bs:1>> (0b ∷ 0b ∷ zs) (b ∷ bs) (_ ∷a _ ∷a zs=0) = 
        cong minusCarry-aux
             (predList<zeroes++<1:bs:1>> (0b ∷ zs) (b ∷ bs) (refl ∷a zs=0)) 

------------------------------------------------------------------------------
++assoc = Monoid.assoc (ListProp.++-monoid Bit)


hasLast1-predList-bbs:1 :  ∀ b bs → HasLast1 (predList ((b ∷ bs) ∷ʳ 1b))
hasLast1-predList-bbs:1 b bs = 
                             aux b bs (search Bit ≟1b (b ∷ bs))
  where
  aux :  ∀ b bs → Search Bit ≟1b (b ∷ bs) → 
                                      HasLast1 (predList ((b ∷ bs) ∷ʳ 1b))
  aux b bs (inj₂ bbs≠1) = 
                      subst HasLast1 (sym eq) hl1-1:map1-bs
    where
    P = (_≢b 1b);   Q = (_≡b 0b);  P⊆Q = \{b} → ≢1b⇒≡0b b

    bbs=0 : All (_≡b 0b) (b ∷ bs)
    bbs=0 = Data.List.All.map P⊆Q bbs≠1  

    b≡0b    = Data.List.All.head bbs=0 
    bs=0    = Data.List.All.tail bbs=0 
    map1-bs = map const-1b bs

    map1-bs=1 : All (_≡b 1b) map1-bs
    map1-bs=1 = all-map-const 1b bs 

    eq :  predList ((b ∷ bs) ∷ʳ 1b) ≡ 1b ∷ (map const-1b bs)
    eq = 
      begin predList ((b ∷ bs) ∷ʳ 1b)    
                                 ≡⟨ cong (\x → predList ((x ∷ bs) ∷ʳ 1b)) b≡0b
                                  ⟩   
            predList ((0b ∷ bs) ∷ʳ 1b)   ≡⟨ predList<0:zeroes:1> bs bs=0 ⟩
            1b ∷ (map const-1b bs)
      ∎

    hl1-1:map1-bs :  HasLast1 (1b ∷ map1-bs)
    hl1-1:map1-bs =  bs=1→hasLast1-1bs map1-bs map1-bs=1

  aux b bs (inj₁ (found′ zrs un rest zrs≠1 un≡1b zrs++un:rest≡bbs)) = 
                                                subst HasLast1 (sym eq) hl1-it
    where
    P = (_≢b 1b);   Q = (_≡b 0b);  P⊆Q = \{b} → ≢1b⇒≡0b b

    zrs=0 : All (_≡b 0b) zrs
    zrs=0 = Data.List.All.map P⊆Q zrs≠1  

    map1-zrs = map const-1b zrs

    eq :  predList ((b ∷ bs) ∷ʳ 1b) ≡
          ((map const-1b zrs) ++ (0b ∷ rest)) ∷ʳ 1b 
    eq = 
      begin 
        predList ((b ∷ bs) ∷ʳ 1b)             ≡⟨ cong (predList ∘ (_∷ʳ 1b))  
                                                      (sym zrs++un:rest≡bbs) ⟩
        predList ((zrs ++ (un ∷ rest)) ∷ʳ 1b)
                           ≡⟨ cong (\x → predList ((zrs ++ (x ∷ rest)) ∷ʳ 1b)) 
                                   un≡1b 
                            ⟩
        predList ((zrs ++ (1b ∷ rest)) ∷ʳ 1b)
                             ≡⟨ cong predList (++assoc zrs (1b ∷ rest) [ 1b ])
                              ⟩
        predList (zrs ++ ((1b ∷ (rest ∷ʳ 1b))))
                                ≡⟨ predList<zeroes++<1:bs:1>> zrs rest zrs=0
                                 ⟩
        (map const-1b zrs) ++ ((0b ∷ rest) ∷ʳ 1b)
                                  ≡⟨ sym (++assoc map1-zrs (0b ∷ rest) [ 1b ])
                                   ⟩
        ((map const-1b zrs) ++ (0b ∷ rest)) ∷ʳ 1b
      ∎

    hl1-it :  HasLast1 ((map1-zrs ++ (0b ∷ rest)) ∷ʳ 1b)
    hl1-it =  hasLast1-bs:1 (map1-zrs ++ (0b ∷ rest))


------------------------------------------------------------------------------
addC1-units :  ∀ {bs} → All (_≡ 1b) bs → addC1 bs ≡ (map const-0b bs) ∷ʳ 1b
addC1-units {[]}      _           =  refl
addC1-units {⊥b ∷ _} 
addC1-units {1b ∷ bs} (_ ∷a bs=1)     =  cong (0b ∷_) (addC1-units bs=1)  
addC1-units {0b ∷ bs} (0b≡1b ∷a bs=1) =  ⊥-elim (0b≢1b 0b≡1b)


----------------------------------------------------------------------
predList∘addC1∘-++1 :  ∀ bs → predList (addC1 (bs ∷ʳ 1b)) ≡ (bs ∷ʳ 1b)
predList∘addC1∘-++1 bs =
                       aux bs (search Bit ≟0b bs)
  where
  aux :  (bs : List Bit) → Search Bit ≟0b bs → 
                           predList (addC1 (bs ∷ʳ 1b)) ≡ (bs ∷ʳ 1b)

  aux []       _            =  refl
  aux (b ∷ bs) (inj₂ bbs≠0) =  
    begin 
      predList (addC1 (b ∷ (bs ∷ʳ 1b)))  
                       ≡⟨ cong predList (addC1-units {b ∷ (bs ∷ʳ 1b)} bbs:1=1)
                        ⟩ 
      predList ((0b ∷ (map const-0b (bs ∷ʳ 1b))) ∷ʳ 1b)   ≡⟨ refl ⟩ 
      predList ((0b ∷ zeroes) ∷ʳ 1b)   
                                 ≡⟨ predList<0:zeroes:1> zeroes zeroes=0 ⟩ 
      1b ∷ units                 ≡⟨ cong (1b ∷_) units≡bs:1 ⟩ 
      1b ∷ (bs ∷ʳ 1b)            ≡⟨ cong (_∷ (bs ∷ʳ 1b)) (sym b≡1b) ⟩ 
      b ∷ (bs ∷ʳ 1b)
    ∎
    where
    P = (_≢b 0b);   Q = (_≡b 1b);  P⊆Q = \{b} → ≢0b⇒≡1b b

    bbs=1 : All (_≡b 1b) (b ∷ bs)
    bbs=1 = Data.List.All.map P⊆Q bbs≠0  

    b≡1b    =  Data.List.All.head bbs=1 
    bbs:1=1 =  AllProp.++⁺ bbs=1 (refl ∷a []a)  
 
    bs:1=1 :  All (_≡b 1b) (bs ∷ʳ 1b)
    bs:1=1 =  Data.List.All.tail bbs:1=1 

    zeroes   = map const-0b (bs ∷ʳ 1b)
    zeroes=0 = all-map-const 0b (bs ∷ʳ 1b)
    units    = map const-1b zeroes

    units=1 : All (_≡b 1b) units
    units=1 = all-map-const 1b zeroes 

    units≡bs:1 :  units ≡ bs ∷ʳ 1b
    units≡bs:1 = 
     begin 
       map const-1b (map const-0b (bs ∷ʳ 1b)) 
                                             ≡⟨ sym (map-compose (bs ∷ʳ 1b)) ⟩ 
       map (const-1b ∘ const-0b) (bs ∷ʳ 1b)       
                      ≡⟨ map-cong {A = Bit} {B = Bit} const1∘const0 (bs ∷ʳ 1b) 
                       ⟩
       map const-1b (bs ∷ʳ 1b)    ≡⟨ all-xs=c→map-c-xs≡xs 1b bs:1=1 ⟩ 
       bs ∷ʳ 1b
     ∎

  aux (b ∷ bs) (inj₁ (found′ uns z rest uns≠0 z≡0b uns++z:rest≡bbs)) =  
    begin
      predList (addC1 ((b ∷ bs) ∷ʳ 1b))       
                                   ≡⟨ cong (\xs → predList $ addC1 (xs ∷ʳ 1b)) 
                                           (sym uns++z:rest≡bbs)
                                    ⟩ 
      predList (addC1 ((uns ++ (z ∷ rest)) ∷ʳ 1b))   
                    ≡⟨ cong (predList ∘ addC1) (++assoc uns (z ∷ rest) [ 1b ])
                     ⟩
      predList (addC1 (uns ++ (z ∷ (rest ∷ʳ 1b))))
                   ≡⟨ cong (\x → predList $ addC1 (uns ++ (x ∷ (rest ∷ʳ 1b))))
                           z≡0b 
                    ⟩ 
      predList (addC1 (uns ++ (0b ∷ (rest ∷ʳ 1b))))   
                  ≡⟨ cong predList (addC1<units++0:bs> uns (rest ∷ʳ 1b) uns=1)
                   ⟩  
      predList (zrs ++ (1b ∷ (rest ∷ʳ 1b)))
                                 ≡⟨ predList<zeroes++<1:bs:1>> zrs rest zrs=0 
                                  ⟩
      (map const-1b zrs) ++ (0b ∷ (rest ∷ʳ 1b)) 
                               ≡⟨ cong (_++ (0b ∷ (rest ∷ʳ 1b))) map-1-zrs≡uns
                                ⟩
      uns ++ (0b ∷ (rest ∷ʳ 1b))    ≡⟨ sym (++assoc uns (0b ∷ rest) [ 1b ]) ⟩
      (uns ++ (0b ∷ rest)) ∷ʳ 1b    ≡⟨ cong (\x → (uns ++ (x ∷ rest)) ∷ʳ 1b)
                                            (sym z≡0b)
                                     ⟩  
      (uns ++ (z ∷ rest)) ∷ʳ 1b     ≡⟨ cong (_∷ʳ 1b) uns++z:rest≡bbs ⟩  
      (b ∷ bs) ∷ʳ 1b                  
    ∎
    where
    P = (_≢b 0b);  Q = (_≡b 1b);  P⊆Q = \{b} → ≢0b⇒≡1b b

    zrs = map const-0b uns

    uns=1 : All (_≡b 1b) uns 
    uns=1 = Data.List.All.map P⊆Q uns≠0  

    zrs=0 = all-map-const 0b uns

    map-1-zrs≡uns :  map const-1b zrs ≡ uns
    map-1-zrs≡uns =
      begin
        map const-1b (map const-0b uns)     ≡⟨ sym (map-compose uns) ⟩ 
        map (const-1b ∘ const-0b) uns     
                           ≡⟨ map-cong {A = Bit} {B = Bit} const1∘const0 uns ⟩ 
        map const-1b uns   ≡⟨ all-xs=c→map-c-xs≡xs 1b uns=1 ⟩ 
        uns
      ∎ 

------------------------------------------------------------------------------
addC1∘predList∘-++1 :  ∀ bs → addC1 (predList (bs ∷ʳ 1b)) ≡ (bs ∷ʳ 1b)
addC1∘predList∘-++1 bs =
                       aux bs (search Bit ≟1b bs)
  where
  aux :  (bs : List Bit) → Search Bit ≟1b bs → 
                           addC1 (predList (bs ∷ʳ 1b)) ≡ (bs ∷ʳ 1b) 

  aux []       _            =  refl
  aux (b ∷ bs) (inj₂ bbs≠1) =  
    begin 
      addC1 (predList ((b ∷ bs) ∷ʳ 1b)) 
                         ≡⟨ cong (\x → addC1 (predList ((x ∷ bs) ∷ʳ 1b))) b≡0b 
                          ⟩
      addC1 (predList ((0b ∷ bs) ∷ʳ 1b))     
                                 ≡⟨ cong addC1 (predList<0:zeroes:1> bs bs=0) 
                                  ⟩
      addC1 (1b ∷ (map const-1b bs))               ≡⟨ addC1-units 1:map-1-bs=1 
                                                    ⟩
      (map const-0b (1b ∷ (map const-1b bs))) ∷ʳ 1b          ≡⟨ refl ⟩
      0b ∷ ((map const-0b (map const-1b bs)) ∷ʳ 1b) 
                           ≡⟨ cong ((0b ∷_) ∘ (_∷ʳ 1b)) (sym (map-compose bs)) 
                            ⟩
      0b ∷ ((map (const-0b ∘ const-1b) bs) ∷ʳ 1b)
                      ≡⟨ cong ((0b ∷_) ∘ (_∷ʳ 1b)) (map-cong const0∘const1 bs)
                       ⟩
      0b ∷ ((map const-0b bs) ∷ʳ 1b)   ≡⟨ cong ((0b ∷_) ∘ (_∷ʳ 1b)) 
                                                          map-0-bs≡bs
                                        ⟩
      0b ∷ (bs ∷ʳ 1b)                  ≡⟨ cong (_∷ (bs ∷ʳ 1b)) (sym b≡0b) ⟩
      (b ∷ bs) ∷ʳ 1b
    ∎
    where
    P = (_≢b 1b);   Q = (_≡b 0b);   P⊆Q = \{b} → ≢1b⇒≡0b b

    bbs=0 : All (_≡b 0b) (b ∷ bs)
    bbs=0 = Data.List.All.map P⊆Q bbs≠1  

    b≡0b = Data.List.All.head bbs=0 
    bs=0 = Data.List.All.tail bbs=0 

    map-1-bbs = map const-1b (b ∷ bs)

    map-1-bbs=1 : All (_≡ 1b) map-1-bbs
    map-1-bbs=1 = all-map-const 1b (b ∷ bs)

    map-1-bs=1   = Data.List.All.tail map-1-bbs=1 
    1:map-1-bs=1 = refl ∷a map-1-bs=1

    map-0-bs≡bs =  all-xs=c→map-c-xs≡xs 0b bs=0 
 
 
  aux (b ∷ bs) (inj₁ (found′ zrs un rest zrs≠1 un≡1b zrs++un:rest≡bbs)) = 
    begin 
      addC1 (predList ((b ∷ bs) ∷ʳ 1b)) 
                  ≡⟨ cong (addC1 ∘ predList ∘ (_∷ʳ 1b)) (sym zrs++un:rest≡bbs)
                   ⟩
      addC1 (predList ((zrs ++ (un ∷ rest)) ∷ʳ 1b))
                   ≡⟨ cong (\x → addC1 (predList ((zrs ++ (x ∷ rest)) ∷ʳ 1b)))
                           un≡1b
                    ⟩
      addC1 (predList ((zrs ++ (1b ∷ rest)) ∷ʳ 1b))
                 ≡⟨ cong (addC1 ∘ predList) (++assoc zrs (1b ∷ rest) [ 1b ])
                  ⟩
      addC1 (predList (zrs ++ ((1b ∷ rest) ∷ʳ 1b)))
                     ≡⟨ cong addC1 (predList<zeroes++<1:bs:1>> zrs rest zrs=0) 
                      ⟩
      addC1 (map1-zrs ++ ((0b ∷ rest) ∷ʳ 1b))   ≡⟨ refl ⟩
      addC1 (map1-zrs ++ (0b ∷ (rest ∷ʳ 1b)))
                       ≡⟨ addC1<units++0:bs> map1-zrs (rest ∷ʳ 1b) map1-zrs=1
                        ⟩
      (map const-0b map1-zrs) ++ (1b ∷ (rest ∷ʳ 1b))  
                           ≡⟨ cong (_++ (1b ∷ (rest ∷ʳ 1b))) map0-map1-zrs≡zrs 
                            ⟩
      zrs ++ ((1b ∷ rest) ∷ʳ 1b)    ≡⟨ sym (++assoc zrs (1b ∷ rest) [ 1b ]) ⟩
      (zrs ++ (1b ∷ rest)) ∷ʳ 1b    ≡⟨ cong (\x → (zrs ++ (x ∷ rest)) ∷ʳ 1b) 
                                            (sym un≡1b) 
                                     ⟩
      (zrs ++ (un ∷ rest)) ∷ʳ 1b    ≡⟨ cong (_∷ʳ 1b) zrs++un:rest≡bbs ⟩
      (b ∷ bs) ∷ʳ 1b
    ∎
    where
    P = (_≢b 1b);   Q = (_≡b 0b);   P⊆Q = \{b} → ≢1b⇒≡0b b

    zrs=0 : All (_≡b 0b) zrs
    zrs=0 = Data.List.All.map P⊆Q zrs≠1  

    map1-zrs   = map const-1b zrs
    map1-zrs=1 = all-map-const 1b zrs

    map0-map1-zrs=0 :  All (_≡ 0b) (map const-0b map1-zrs)
    map0-map1-zrs=0 =  all-map-const 0b map1-zrs

    map0-map1-zrs≡zrs = 
       begin 
         map const-0b (map const-1b zrs)   ≡⟨ sym (map-compose zrs) ⟩ 
         map (const-0b ∘ const-1b) zrs     ≡⟨ map-cong const0∘const1 zrs ⟩ 
         map const-0b zrs                  ≡⟨ all-xs=c→map-c-xs≡xs 0b zrs=0 ⟩ 
         zrs
       ∎  


------------------------------------------------------------------------------
pred∘suc :  pred ∘ suc ≗ id

pred∘suc 0#      =  refl
pred∘suc (bs 1#) = 
  begin
    pred (fromBits (addBL 0b [ 1b ] (toBits (bs 1#))))  
                                ≡⟨ cong (pred ∘ fromBits) ([1b]+ (bs ∷ʳ 1b)) 
                                 ⟩ 
    pred (fromBits (addC1 (bs ∷ʳ 1b)))                            ≡⟨ refl ⟩  
    fromBits (predList (toBits (fromBits (addC1 (bs ∷ʳ 1b)))))
                               ≡⟨ cong (fromBits ∘ predList)
                                       (toBits∘fromBits (addC1 (bs ∷ʳ 1b)) 
                                       (hasLast1-addC1 (bs ∷ʳ 1b) hl1if-bs:1)) 
                                ⟩  
    fromBits (predList (addC1 (bs ∷ʳ 1b)))
                                   ≡⟨ cong fromBits (predList∘addC1∘-++1 bs) ⟩
    fromBits (bs ∷ʳ 1b)            ≡⟨ fromBits-bs:1 bs ⟩
    bs 1#
  ∎
  where 
  hl1-bs:1   = hasLast1-bs:1 bs 
  hl1if-bs:1 = hasLast1→hasLast1if (bs ∷ʳ 1b) hl1-bs:1 

--------------------------------------------------------
suc∘pred :  (bs : List Bit) → suc (pred (bs 1#)) ≡ bs 1#
suc∘pred []       =  refl 
suc∘pred (b ∷ bs) =  goal
  where
  bbs             = b ∷ bs
  hl1-pred<bbs:1> = hasLast1-predList-bbs:1 b bs

  goal :  suc (pred (bbs 1#)) ≡ bbs 1#
  goal = 
    begin 
      suc (pred (bbs 1#))                    ≡⟨ suc-as-addC1 (pred (bbs 1#)) ⟩
      fromBits (addC1 (toBits (pred (bbs 1#))))                    ≡⟨ refl ⟩
      fromBits (addC1 (toBits (fromBits (predList (bbs ∷ʳ 1b)))))
               ≡⟨ cong (fromBits ∘ addC1)
                    (toBits∘fromBits (predList (bbs ∷ʳ 1b)) hl1-pred<bbs:1>)
                ⟩
      fromBits (addC1 (predList (bbs ∷ʳ 1b)))     
                                  ≡⟨ cong fromBits (addC1∘predList∘-++1 bbs) ⟩
      fromBits (bbs ∷ʳ 1b)        ≡⟨ fromBits-bs:1 bbs ⟩
      bbs 1#
    ∎

suc∘pred-for>0 :  ∀ {x} → 0# < x → suc (pred x) ≡ x

suc∘pred-for>0 {0#}    0<0 =  ⊥-elim (<-irrefl (refl {x = 0#}) 0<0)
suc∘pred-for>0 {bs 1#} 0<0 =  suc∘pred bs
                       

------------------------------------------------------------------------------
fromDigs = fromDigits {2} 

fromDigits>0 : (bs : Bin⁺) → HasLast1 bs → fromDigs bs >n 0
fromDigits>0 []            ()
fromDigits>0 (0b ∷ [])     ()
fromDigits>0 (1b ∷ [])     _          =  0<1+n
fromDigits>0 (⊥b ∷ _)      _
fromDigits>0 (1b ∷ _)      _          =  0<1+n
fromDigits>0 (0b ∷ b ∷ bs) hl1-0:b:bs =
    ≤begin
         1                           ≤[ fromDigits>0 (b ∷ bs) hl1-b:bs ]
         fromDigs (b ∷ bs)           ≤[ n≤n*2 _ ]
         fromDigs (b ∷ bs) *n 2     ≡≤[ refl ]
         fromDigs (zero ∷ b ∷ bs)
    ≤end
    where 
    hl1-b:bs : HasLast1 (b ∷ bs)
    hl1-b:bs = hl1-0:b:bs

    1≤2 = NatP.n≤1+n 1

    n≤n*2 : ∀ n → (n ≤n n *n 2)
    n≤n*2 n = ≤begin  n         ≡≤[ sym (*-identityˡ n) ]
                      1 *n n     ≤[ *-mono-≤ 1≤2 (≤-refl {n}) ]
                      2 *n n    ≡≤[ *n-comm 2 n ]
                      n *n 2
              ≤end

---------------------------------------------------------------
0<fromDigits-bs:1 :  (bs : List Bit) → 0 <n fromDigs (bs ∷ʳ 1b)

0<fromDigits-bs:1 []        =  0<1+n
0<fromDigits-bs:1 (⊥b ∷ _)  
0<fromDigits-bs:1 (0b ∷ bs) =  
    ≤begin
      1                             ≤[ 0<fromDigits-bs:1 bs ]
      fromDigs (bs ∷ʳ 1b)          ≡≤[ sym (*1 (fromDigs (bs ∷ʳ 1b))) ]
      (fromDigs (bs ∷ʳ 1b)) *n 1    ≤[ *-mono-≤ (≤-refl {fromDigs (bs ∷ʳ 1b)})
                                                (s≤s z≤n) ] 
      (fromDigs (bs ∷ʳ 1b)) *n 2  
    ≤end

0<fromDigits-bs:1 (1b ∷ bs) =  m≤m+n 1 ((fromDigs (bs ∷ʳ 1b)) *n 2)


0<toℕ-bs1 :  ∀ bs → 0 <n toℕ (bs 1#)
0<toℕ-bs1 bs = 
             0<fromDigits-bs:1 bs 

toℕ-bs1≢0 :  ∀ bs → toℕ (bs 1#) ≢ 0 
toℕ-bs1≢0 bs = 
             ≢sym (NatP.<⇒≢ (0<toℕ-bs1 bs))


------------------------------------------------------------------------------
0≢fromDigits : ∀ b bs → HasLast1if (b ∷ bs) → 0 ≢ fromDigs (b ∷ bs)
0≢fromDigits b bs hl1if-b:bs =  0≢-b:bsN 
             where
             0≢-b:bsN :  0 ≢ fromDigs (b ∷ bs)
             0≢-b:bsN =  <⇒≢ 0<b:bsN
                         where
                         hasLast1-b:bs = hasLast1if→hasLast1 b bs hl1if-b:bs

                         0<b:bsN : 0 <n fromDigits (b ∷ bs)
                         0<b:bsN = fromDigits>0 (b ∷ bs) hasLast1-b:bs

------------------------------------------------------------------------------
injective-fromDigits : ∀ {bs bs'} → HasLast1if bs → HasLast1if bs' →
                                    fromDigs bs ≡ fromDigs bs' → bs ≡ bs'

injective-fromDigits {[]} {[]}     _ _          _       =  refl
injective-fromDigits {[]} {b ∷ bs} _ hl1if-b:bs 0=b:bsN =
                                         ⊥-elim (0≢fromDigits b bs hl1if-b:bs
                                                                      0=b:bsN)
injective-fromDigits {b ∷ bs} {[]} hl1if-b:bs _ b:bsN=0 =
                                       ⊥-elim $ 0≢fromDigits b bs hl1if-b:bs $
                                                                  sym b:bsN=0

injective-fromDigits {b ∷ bs} {b' ∷ bs'} hl1-b:bs hl1-b':bs' b:bs-N=b':bs'-N
  with
      b ≟b b'

... | yes b=b' =  cong₂ _∷_ b=b' bs=bs'
      where
      hasLast1if-bs  = hasLast1if-tail0 (b ∷ bs)   hl1-b:bs
      hasLast1if-bs' = hasLast1if-tail0 (b' ∷ bs') hl1-b':bs'

      bN  = Fin.toℕ b
      b'N = Fin.toℕ b'

      bN=b'N :  bN ≡ b'N
      bN=b'N =  cong Fin.toℕ b=b'

      bsN  = fromDigits bs
      bs'N = fromDigits bs'

      bsN*2=bs'N*2 : bsN *n 2 ≡ bs'N *n 2
                                         -- use  b:bs-N=b':bs'-N  for
      bsN*2=bs'N*2 =                     -- fromDigits (b ∷ bs) = bN+bsN*2 ≡..
        begin
          bsN *n 2                   ≡⟨ sym (m+n∸n≡m _ bN) ⟩
          (bsN *n 2 +n bN) ∸ bN      ≡⟨ cong (_∸ bN) (+n-comm _ bN) ⟩
          (bN +n bsN *n 2) ∸ bN      ≡⟨ cong (_∸ bN) b:bs-N=b':bs'-N ⟩
          (b'N +n bs'N *n 2) ∸ bN    ≡⟨ cong ((b'N +n bs'N *n 2) ∸_) bN=b'N ⟩
          (b'N +n bs'N *n 2) ∸ b'N   ≡⟨ cong (_∸ b'N) (+n-comm b'N _) ⟩
          (bs'N *n 2 +n b'N) ∸ b'N   ≡⟨ m+n∸n≡m _ b'N ⟩
          bs'N *n 2
        ∎

      bsN=bs'N :  bsN ≡ bs'N
      bsN=bs'N =  begin bsN                ≡⟨ sym $ half<n*2> bsN ⟩
                        half (bsN *n 2)    ≡⟨ cong half bsN*2=bs'N*2 ⟩
                        half (bs'N *n 2)   ≡⟨ half<n*2> bs'N ⟩
                        bs'N
                  ∎

      bs=bs' = injective-fromDigits {bs} {bs'} hasLast1if-bs hasLast1if-bs'
                                                             bsN=bs'N

... | no b≢b'       -- to be rejected
      with b | b'

...   | _  | ⊥b
...   | ⊥b | _
...   | 0b | 0b =  ⊥-elim (b≢b' refl)
...   | 1b | 1b =  ⊥-elim (b≢b' refl)
...   | 0b | 1b =  ⊥-elim (odd-1+bs'N*2 even-1+bs'N*2)
                        -- bsN * 2  ≡  1 + bs'N * 2
                        -- contradicts to  Even lhs × Odd rhs
                   where
                   bsN          = fromDigits bs
                   bs'N         = fromDigits bs'
                   even-bsN*2   = even-2* bsN
                   even-bs'N*2  = even-2* bs'N
                   odd-1+bs'N*2 = odd-suc even-bs'N*2

                   even-1+bs'N*2 : Even (1 +n bs'N *n 2)
                   even-1+bs'N*2 = subst Even b:bs-N=b':bs'-N even-bsN*2

...   | 1b | 0b =  ⊥-elim (odd-1+bsN*2 even-1+bsN*2)
            where
            bsN         = fromDigits bs
            bs'N        = fromDigits bs'
            even-bsN*2  = even-2* bsN
            even-bs'N*2 = even-2* bs'N
            odd-1+bsN*2 = odd-suc even-bsN*2

            even-1+bsN*2 : Even (1 +n bsN *n 2)
            even-1+bsN*2 = subst Even (sym b:bs-N=b':bs'-N) even-bs'N*2


------------------------------------------------------------------------------
toBDigits : (n : ℕ) → ∃ \ (bs : Bin⁺) → fromDigits bs ≡ n × HasLast1if bs
--
-- Re-implementing  toDigits  for  base = 2  and  0 <--> [].
-- We hope that proofs for  toBDigits  will be simpler than for  toDigits.

toBDigits n =  toBits' n n ≤-refl
  where
  toBits' : (n counter : ℕ) → n ≤n counter → ∃ \ (bs : Bin⁺) →
                                             fromDigits bs ≡ n × HasLast1if bs
  -- counter  is for termination proof; it decreases with each division by 2;
  --          and it holds counter ≡ 0 ==> n ≡ 0.

  toBits' 0      _        _       =  ([] , refl ,    ⊤.tt)
  toBits' _      0        n≤0     =  ([] , sym n=0 , ⊤.tt)  where
                                                              n=0 = ≤0⇒≡0 n≤0
  toBits' (1+ n) (1+ cnt) n'≤cnt' =  (r ∷ bs , from-r:bs=n' , hl1if-r:bs)
    where
    open DM.DivMod

    n'   = 1+ n
    cnt' = 1+ cnt
    res  = n' divMod 2
    q    = quotient res

    r : Fin 2
    r = remainder res

    rN        = Fin.toℕ r
    n'=rN+q*2 = property res
    half-cnt' = half cnt'

    q=half-n' :  q ≡ half n'
    q=half-n' =  sym $ half-n=n-div-2 n'

    q≤cnt : q ≤n cnt
    q≤cnt = ≤begin  q           ≡≤[ q=half-n' ]
                    half n'      ≤[ ⌊n/2⌋-mono n'≤cnt' ]
                    half cnt'    ≤[ half-suc-n≤n cnt ]
                    cnt
            ≤end

    pair      = toBits' q cnt q≤cnt
    bs        = proj₁ pair
    from-bs=q = proj₁ $ proj₂ pair
    hl1if-bs  = proj₂ $ proj₂ pair

    from-r:bs=n' :  fromDigits (r ∷ bs) ≡ n'
    from-r:bs=n' =
           begin
             fromDigits (r ∷ bs)            ≡⟨ refl ⟩
             rN +n ((fromDigits bs) *n 2)   ≡⟨ cong ((rN +n_) ∘ (_*n 2))
                                                                from-bs=q ⟩
             rN +n (q *n 2)                 ≡⟨ sym n'=rN+q*2 ⟩
             n'
           ∎

    hl1-r:bs : HasLast1 (r ∷ bs)
    hl1-r:bs = go r bs hl1if-bs from-r:bs=n'
      where
      go : (r : Bit) → (bs : Bin⁺) → HasLast1if bs →
                             fromDigits (r ∷ bs) ≡ n' → HasLast1 (r ∷ bs)
      go ⊥b
      go _  (b ∷ bs') hl1if-bs _          =  hasLast1if→hasLast1
                                                           b bs' hl1if-bs
      go 1b []        _        _          =  refl
      go 0b []        _        from[0]=n' =  ⊥-elim $ n'/=0 n'=0
         where
         n'/=0 = >⇒≢ (0<1+n {n})

         n'=0 : n' ≡ 0
         n'=0 = begin  n'                             ≡⟨ sym from[0]=n' ⟩
                       fromDigits ((zero {2}) ∷ [])   ≡⟨ refl ⟩
                       0
                ∎

    hl1if-r:bs : HasLast1if (r ∷ bs)
    hl1if-r:bs = hasLast1→hasLast1if (r ∷ bs) hl1-r:bs

------------------------------------------------------------------------------
toBDigs : ℕ → Bin⁺
toBDigs = proj₁ ∘ toBDigits

fromDigits∘toBDigs :  fromDigits ∘ toBDigs ≗ id
fromDigits∘toBDigs =  proj₁ ∘ proj₂ ∘ toBDigits
--
-- Two equations for the two mutually inverse bijections for
--                                            ℕ  <->  Bin⁺ ∩ HasLast1if
--
toBDigs∘fromDigits : {bs : Bin⁺} → HasLast1if bs →
                                                 toBDigs (fromDigits bs) ≡ bs
toBDigs∘fromDigits {[]}      _         =  refl
toBDigs∘fromDigits {b ∷ bs} hl1if-b:bs =
  case
      toBDigits n
  of \
  { (bs' , (from-bs'=n , _)) → injective-fromDigits hl1if-b+n*2 hl1if-b:bs 
                                                  from-toBDigs-b+n*2=from-b:bs
  }
  where
  n           = fromDigits bs
  bN          = Fin.toℕ b
  b+n*2       = bN +n n *n 2
  hl1if-b+n*2 = proj₂ $ proj₂ $ toBDigits b+n*2

  from-toBDigs-b+n*2=from-b:bs :  fromDigits (toBDigs b+n*2) ≡
                                                          fromDigits (b ∷ bs)
  from-toBDigs-b+n*2=from-b:bs =  trans (fromDigits∘toBDigs b+n*2) refl


------------------------------------------------------------------------------
fromDigits-suc-eq : {bs : Bin⁺} → fromDigits (addC1 bs) ≡ 1+ (fromDigits bs)

fromDigits-suc-eq {[]}      =  refl
fromDigits-suc-eq {⊥b ∷ _}
fromDigits-suc-eq {0b ∷ bs} =  refl
                       -- 1 + (fromDigits (bs) * 2 ≡ suc ((fromDigits bs) * 2)
fromDigits-suc-eq {1b ∷ bs} =  cong (_*n 2) $ fromDigits-suc-eq {bs}
  -- because the goal
  --         (fromDigits (addC1 bs)) * 2  ≡  suc (suc ((fromDigits bs) * 2))
  -- is normalized to  ...
  --         (fromDigits (addC1 bs)) * 2  ≡  suc (1 + (fromDigits bs) * 2),
  -- and then the recursive proof is applied in LHS.

-- fromDigits-suc-eq  and  toBDigs-suc-eq   prove the two isomorphisms for
--                                                   ℕ  <->  Bin⁺ ∩ HasLast1if

fromDigits-pred-eq :  
           {bs : Bin⁺} → 
           fromDigits (predList (bs ∷ʳ 1b)) ≡ predN (fromDigits (bs ∷ʳ 1b))

fromDigits-pred-eq {bs} =  cong predN eq
  where
  n        = fromDigits (bs ∷ʳ 1b)
  hl1-bs:1 = hasLast1-bs:1 bs 
  n>0      = fromDigits>0 (bs ∷ʳ 1b) hl1-bs:1 

  eq :  1+ (fromDigits (predList (bs ∷ʳ 1b))) ≡ 
        1+ (predN (fromDigits (bs ∷ʳ 1b)))
  eq = 
   begin
    1+ (fromDigits (predList (bs ∷ʳ 1b)))   
                              ≡⟨ sym (fromDigits-suc-eq {predList (bs ∷ʳ 1b)}) 
                               ⟩
    fromDigits (addC1 (predList (bs ∷ʳ 1b)))  ≡⟨ cong fromDigits 
                                                    (addC1∘predList∘-++1 bs) ⟩
    fromDigits (bs ∷ʳ 1b)                     ≡⟨ sym (NatProp0.suc∘pred n>0) ⟩
    1+ (predN (fromDigits (bs ∷ʳ 1b)))
   ∎

------------------------------------------------------------------------------
toBDigs-suc-eq :  {n : ℕ} → toBDigs (1+ n) ≡ addC1 (toBDigs n)
toBDigs-suc-eq {n}  with  toBDigits n
...
    | (bs , (from-bs=n , hl1if-bs)) =  goal
    where
    bs'       = addC1 bs
    hl1if-bs' = hasLast1→hasLast1if bs' $ hasLast1-addC1 bs hl1if-bs

    e : fromDigits bs' ≡ 1+ n
    e = begin  fromDigits bs'       ≡⟨ fromDigits-suc-eq {bs} ⟩
               1+ (fromDigits bs)   ≡⟨ cong 1+_ from-bs=n ⟩
               1+ n
        ∎

    goal : toBDigs (1+ n) ≡ addC1 bs
    goal = begin
             toBDigs (1+ n)             ≡⟨ cong toBDigs $ sym e ⟩
             toBDigs (fromDigits bs')   ≡⟨ toBDigs∘fromDigits hl1if-bs' ⟩
             bs'
           ∎

------------------------------------------------------------------------------
fromℕ :  ℕ → Bin
fromℕ n =  fromBits (toBDigs n)

toBits≗toBDigs∘toℕ :  {a : Bin} → a ≢ 0# → toBits a ≡ toBDigs (toℕ a) 
toBits≗toBDigs∘toℕ {a} a≢0# =           
  begin
    toBits a                  ≡⟨ sym (toBDigs∘fromDigits hasLast1if-bs) ⟩
    toBDigs (fromDigits bs)   ≡⟨ refl ⟩  
    toBDigs (toℕ a)
  ∎
  where bs            = toBits a
        hasLast1if-bs = hasLast1→hasLast1if bs (hasLast1∘toBits a≢0#)


------------------------------------------------------------------------------
-- Prove that the maps    ℕ --fromℕ-> Bin   
-- and                      <--toℕ--        are mutulally inverse.
--
-- (And it is easy to prove from this that they are bijections).

fromℕ∘toℕ :  fromℕ ∘ toℕ ≗ id

fromℕ∘toℕ 0#      =  refl
fromℕ∘toℕ (bs 1#) = 
  begin
    fromℕ (toℕ (bs 1#))                          ≡⟨ refl ⟩
    fromBits (toBDigs (fromDigits (bs ∷ʳ 1b)))
                           ≡⟨ cong fromBits 
                                   (toBDigs∘fromDigits {bs ∷ʳ 1b} hl1if-bs:1)
                            ⟩
    fromBits (bs ∷ʳ 1b)    ≡⟨ fromBits-bs:1 bs ⟩
    bs 1#
  ∎
  where hl1-bs:1   = hasLast1-bs:1 bs
        hl1if-bs:1 = hasLast1→hasLast1if (bs ∷ʳ 1b) hl1-bs:1 


toℕ∘fromℕ :  toℕ ∘ fromℕ ≗ id

toℕ∘fromℕ 0      =  refl
toℕ∘fromℕ (1+ n) = 
  let 
    (bs , _ , hl1if-bs) = toBDigits n
    bs'                 = addC1 (toBDigs n)
    hl1if-bs'           = hasLast1-addC1 bs hl1if-bs 
  in
  begin
    toℕ (fromℕ (1+ n))                                   ≡⟨ refl ⟩
    fromDigits (toBits (fromBits (toBDigs (1+ n)))) 
                                     ≡⟨ cong (fromDigits ∘ toBits ∘ fromBits)  
                                             (toBDigs-suc-eq {n}) 
                                      ⟩
    fromDigits (toBits (fromBits (addC1 (toBDigs n))))
                            ≡⟨ cong fromDigits (toBits∘fromBits bs' hl1if-bs') 
                             ⟩ 
    fromDigits (addC1 (toBDigs n))   ≡⟨ cong fromDigits $  
                                             sym (toBDigs-suc-eq {n}) 
                                      ⟩
    fromDigits (toBDigs (1+ n))      ≡⟨ fromDigits∘toBDigs (1+ n) ⟩
    1+ n
  ∎

---------------------------------------
toℕ-x≡0⇒x≡0 :  ∀ x → toℕ x ≡ 0 → x ≡ 0#
toℕ-x≡0⇒x≡0 x xN≡0 = 
                   begin x               ≡⟨ sym (fromℕ∘toℕ x) ⟩
                         fromℕ (toℕ x)   ≡⟨ cong fromℕ xN≡0 ⟩
                         fromℕ 0         ≡⟨ refl ⟩
                         0#
                   ∎
                     

------------------------------------------------------------------------------
-- Prove that fromℕ and toℕ are ring homomorphism.

suc-as-sucN :  suc ≗ fromℕ ∘ 1+_ ∘ toℕ 

suc-as-sucN 0#      =  refl
suc-as-sucN (bs 1#) =
  sym $ 
  begin 
    fromℕ (1+ (toℕ (bs 1#)))                             ≡⟨ refl ⟩
    fromBits (toBDigs (1+ (fromDigits (bs ∷ʳ 1b))))   
                                        ≡⟨ cong fromBits (toBDigs-suc-eq {n}) 
                                         ⟩
    fromBits (addC1 (toBDigs (fromDigits (bs ∷ʳ 1b))))
                                 ≡⟨ cong (fromBits ∘ addC1) 
                                         (toBDigs∘fromDigits {bs'} hl1if-bs:1)
                                  ⟩
    fromBits (addC1 (bs ∷ʳ 1b))         ≡⟨ refl ⟩
    fromBits (addC1 (toBits (bs 1#)))   ≡⟨ sym (suc-as-addC1 (bs 1#)) ⟩
    suc (bs 1#)
  ∎
  where
  bs'        = bs ∷ʳ 1b
  n          = fromDigits bs'
  hl1-bs:1   = hasLast1-bs:1 bs 
  hl1if-bs:1 = hasLast1→hasLast1if (bs ∷ʳ 1b) hl1-bs:1 


toℕ-suc-homo :  toℕ ∘ suc ≗ 1+_ ∘ toℕ 
toℕ-suc-homo a =
        begin toℕ (1' + a)                ≡⟨ cong toℕ (suc-as-sucN a) ⟩
              toℕ (fromℕ (1+_ (toℕ a)))   ≡⟨ toℕ∘fromℕ (1 +n (toℕ a))  ⟩
              1+ (toℕ a)
        ∎

fromℕ-suc-homo :  fromℕ ∘ 1+_ ≗ suc ∘ fromℕ 
fromℕ-suc-homo n =
      begin fromℕ (1+ n)         ≡⟨ cong (fromℕ ∘ 1+_) (sym (toℕ∘fromℕ n)) ⟩
            fromℕ (1+ aN)        ≡⟨ cong fromℕ (sym (toℕ-suc-homo a)) ⟩
            fromℕ (toℕ (suc a))  ≡⟨ fromℕ∘toℕ (suc a) ⟩
            suc a
      ∎
      where  a = fromℕ n;  aN = toℕ a

-------------------------------------------
pred-as-predN :  pred ≗ fromℕ ∘ predN ∘ toℕ 
pred-as-predN 0#      =  refl
pred-as-predN (bs 1#) =     
  begin 
    pa                             ≡⟨ sym (pred∘suc pa) ⟩
    pred (suc pa)                  ≡⟨ eq ⟩
    fromℕ (predN (toℕ (suc pa)))   ≡⟨ cong (fromℕ ∘ predN ∘ toℕ) 
                                           (suc∘pred bs) ⟩
    fromℕ (predN (toℕ a))
  ∎
  where
  a = bs 1#;  pa = pred a

  eq : pred (suc pa) ≡ fromℕ (predN (toℕ (suc pa)))
  eq = begin
         pred (suc pa)                  ≡⟨ pred∘suc pa ⟩
         pa                             ≡⟨ sym (fromℕ∘toℕ pa) ⟩ 
         fromℕ (toℕ pa)                 ≡⟨ refl ⟩ 
         fromℕ (predN (1+ (toℕ pa)))    ≡⟨ cong (fromℕ ∘ predN) $  
                                                sym (toℕ-suc-homo pa) ⟩
         fromℕ (predN (toℕ (suc pa)))
       ∎

toℕ-pred-homo :  toℕ ∘ pred ≗ predN ∘ toℕ 
toℕ-pred-homo a = 
         begin toℕ (pred a)                 ≡⟨ cong toℕ (pred-as-predN a) ⟩
               toℕ (fromℕ (predN (toℕ a)))  ≡⟨ toℕ∘fromℕ (predN (toℕ a)) ⟩
               predN (toℕ a) 
         ∎

------------------------------------------------------------------------------
toℕ+homo :  (a b : Bin) →  toℕ (a + b) ≡ (toℕ a) +n (toℕ b) 
toℕ+homo a b =  
             aux a b (toℕ a) refl
  where
  aux : (a : Bin) → (b : Bin) → (cnt : ℕ) → toℕ a ≡ cnt → 
                                            toℕ (a + b) ≡ (toℕ a) +n (toℕ b)
  -- cnt  is a counter used in termination proof

  aux 0#      b _ _    =  cong toℕ (0+ b)
  aux (bs 1#) _ 0 aN≡0 =  ⊥-elim (NatProp0.>⇒≢ 0<aN aN≡0)  
                          where
                          0<aN = 0<toℕ-bs1 bs 

  aux (bs 1#) b (1+ cnt) a'N≡cnt' =  
    begin
      toℕ (a' + b)                  ≡⟨ cong (toℕ ∘ (_+ b)) $ 
                                            sym (suc∘pred bs) ⟩
      toℕ ((suc pa') + b)           ≡⟨ cong toℕ (suc-assoc (pred a') b) ⟩
      toℕ (suc (pa' + b))           ≡⟨ toℕ-suc-homo (pa' + b) ⟩
      1+ (toℕ (pa' + b))            ≡⟨ cong 1+_ (aux pa' b cnt toℕ-pa'≡cnt) ⟩ 
      1+ ((toℕ pa') +n (toℕ b))     ≡⟨ cong (\x → 1+ (x +n (toℕ b))) 
                                                         (toℕ-pred-homo a') ⟩ 
      1+ ((predN (toℕ a')) +n (toℕ b))   ≡⟨ refl ⟩
      (1+ (predN (toℕ a'))) +n (toℕ b)   ≡⟨ cong (_+n (toℕ b))  
                                                 (NatProp0.suc∘pred 0<a'N) ⟩
      (toℕ a') +n (toℕ b) 
    ∎
    where
    a' = bs 1#;   pa' = pred a';   0<a'N = 0<toℕ-bs1 bs 

    toℕ-pa'≡cnt :  toℕ (pred a') ≡ cnt 
    toℕ-pa'≡cnt =  begin toℕ (pred a')     ≡⟨ toℕ-pred-homo a' ⟩
                         predN (toℕ a')    ≡⟨ cong predN a'N≡cnt' ⟩
                         predN (1+ cnt)    ≡⟨ refl ⟩
                         cnt
                   ∎ 

fromℕ+homo :  (m n : ℕ) →  fromℕ (m +n n) ≡ (fromℕ m) + (fromℕ n) 
fromℕ+homo m n =
           begin 
             fromℕ (m +n n)           ≡⟨ cong fromℕ (cong₂ _+n_ m≡xN n≡yN) ⟩
             fromℕ (toℕ x +n toℕ y)   ≡⟨ cong fromℕ (sym (toℕ+homo x y)) ⟩
             fromℕ (toℕ (x + y))      ≡⟨ fromℕ∘toℕ (x + y)⟩
             x + y
           ∎
           where
           x    = fromℕ m;             y    = fromℕ n
           m≡xN = sym (toℕ∘fromℕ m);   n≡yN = sym (toℕ∘fromℕ n)

------------------------------------------------------------------------------
-- Commutativity and associativity for _+_ are proved by using the isomorphism 
-- to ℕ.

module FP-Bin = FuncProp (_≡_ {A = Bin})

+-comm :  FP-Bin.Commutative _+_
+-comm a b = 
      begin a + b                    ≡⟨ sym (fromℕ∘toℕ (a + b)) ⟩ 
            fromℕ (toℕ (a + b))      ≡⟨ cong fromℕ (toℕ+homo a b) ⟩
            fromℕ (toℕ a +n toℕ b)   ≡⟨ cong fromℕ (+n-comm (toℕ a) (toℕ b)) ⟩
            fromℕ (toℕ b +n toℕ a)   ≡⟨ cong fromℕ (sym (toℕ+homo b a)) ⟩
            fromℕ (toℕ (b + a))      ≡⟨ fromℕ∘toℕ (b + a) ⟩ 
            b + a
      ∎ 

+-assoc :  FP-Bin.Associative _+_
+-assoc a b c = 
  begin 
    (a + b) + c                  ≡⟨ sym (fromℕ∘toℕ ((a + b) + c)) ⟩ 
    fromℕ (toℕ ((a + b) + c))    ≡⟨ cong fromℕ (toℕ+homo (a + b) c) ⟩
    fromℕ (toℕ (a + b) +n cN)    ≡⟨ cong (fromℕ ∘ (_+n cN)) (toℕ+homo a b) ⟩
    fromℕ ((aN +n bN) +n cN)     ≡⟨ cong fromℕ (+n-assoc aN bN cN) ⟩
    fromℕ (aN +n (bN +n cN))     ≡⟨ cong (fromℕ ∘ (aN +n_)) 
                                                  (sym (toℕ+homo b c)) ⟩
    fromℕ (aN +n toℕ (b + c))    ≡⟨ cong fromℕ (sym (toℕ+homo a (b + c))) ⟩
    fromℕ (toℕ (a + (b + c)))    ≡⟨ fromℕ∘toℕ (a + (b + c)) ⟩ 
    (a + (b + c))
  ∎
  where
  aN = toℕ a;   bN = toℕ b;   cN = toℕ c
 

------------------------------------------------------------------------------
{-
downFrom : Bin → Bin → List Bin   -- the full decreasing list  [up .. low]
downFrom up low =
                aux up (toℕ up) refl
  where
  aux :  (x : Bin) → (cnt : ℕ) → toℕ x ≡ cnt → List Bin
  aux 0#      _        _         =  [ 0# ]
  aux (bs 1#) 0        bs1N≡0    =  ⊥-elim (toℕ-bs1≢0 bs bs1N≡0)
  aux (bs 1#) (1+ cnt) bs1N≡cnt' =
      case
          (bs 1#) ≟ low
      of \ 
      { (yes _) → [ low ]
      ; (no _)  → let bs1 = bs 1#

                      eq :  toℕ (pred bs1) ≡ cnt
                      eq =  begin toℕ (pred bs1)   ≡⟨ toℕ-pred-homo bs1 ⟩
                                  predN (toℕ bs1)  ≡⟨ cong predN bs1N≡cnt' ⟩
                                  predN (1+ cnt)   ≡⟨ refl ⟩
                                  cnt
                            ∎
                  in
                  bs1 ∷ (aux (pred bs1) cnt eq)
      }
-}

