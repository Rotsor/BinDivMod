{-                                                            
This file is a part of the library  Binary-3.1.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.  

Binary-3.1  is free software: you can redistribute it and/or modify it 
under the terms of the GNU General Public License.
See  license.txt.
-}

{-# OPTIONS --termination-depth=2 #-}

module Bin4 where

open import Function         using (id; const; _∘_; _$_; case_of_)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Binary  using (Reflexive; Symmetric; Tri; DecSetoid; 
                                    DecTotalOrder; _Preserves_⟶_; 
                                                   _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as PE 
           using (_≡_; _≢_; _≗_; subst; subst₂; cong; cong₂; refl; sym; trans)

open PE.≡-Reasoning renaming (begin_ to begin≡_; _∎ to _end≡) 
open import Data.Empty   using (⊥-elim)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.List    using (List; []; _∷_; _∷ʳ_; [_]; _++_; map)
                                       renaming (length to ln; reverse to rev)
open import Data.List.Properties using (length-++; length-map; length-reverse;
                                                          reverse-++-commute)
open import Data.List.Any using (Any)
import Data.List.Membership.Setoid as Membership
open import Data.List.All using (All; all) renaming ([] to []a)
open import Data.List.All.Properties using (¬All⇒Any¬)
import Relation.Binary.List.Pointwise as Pointwise
import Data.List.Relation.Lex.Strict as StrictLex
import Data.Fin as Fin 
import Data.Fin.Properties as FinP 
open import Data.Digit using (Bit; fromDigits)
open import Data.Nat using (ℕ; z≤n; s≤s; _^_) 
            renaming (suc to 1+_; _+_ to _+n_; pred to predN; _*_ to _*n_; 
                      _≤_ to _≤n_; _<_ to _<n_; _>_ to _>n_; _∸_ to _∸n_ 
                     )
open import Data.Nat.Properties as NatP using (m≤m+n; m+n∸n≡m; m+n∸m≡n)
     renaming (+-assoc to +n-assoc; +-comm to +n-comm; *-comm to *n-comm; 
               +-mono-≤ to +n-mono-≤; *-mono-≤ to *n-mono-≤; 
               pred-mono to predN-mono; *-distribʳ-+ to *n-rDistrib; 
               ≤-refl to ≤n-refl; ≤-reflexive to ≤n-reflexive; 
               ≤-trans to ≤n-trans; ≤-antisym to ≤n-antisym; 
               <-irrefl to <n-irrefl; <-asym to <n-asym; 
               module ≤-Reasoning to ≤n-Reasoning
              )
open ≤n-Reasoning using () renaming (begin_ to ≤nBegin_; _∎ to _≤nEnd;
                                     _≡⟨_⟩_ to _≡≤n[_]_; _≤⟨_⟩_ to _≤n[_]_)

-- of application ---
open import LtReasoning using (module InequalityReasoning)  -- by U. Norell
open import NatProp0    using (natSTO; 0<1+n; suc≢0; pred-n≤n; 2^-mono-≤;
                                                  m<n⇒0<n∸m; m<n⇒k+m*k≤n*k)
open import List0 using (length-xs:x; all-map-const; reverse-injective-≡;
                         Found; found′; findExisting
                        )
open import Bin0 using (Bin; _≡b_; _≢b_; 0b; ⊥b; 1b; toBits; _*2; 2^_; 
                        fromBits-aux; fromBits; suc; pred; predList; toℕ;
                        _<_; _>_; _≤_; _←→_; _+_; _*_; bitLength; const-1b;
                        _≟b_; bitSetoid
                       )
                       renaming (lexBit< to lex<; 1bin to 1'; 2bin to 2')
open import Bin1 using 
     (≢sym; 1b≢0b; ≢0b⇒≡1b; ≢1b⇒≡0b; _bit<_; <-cmp; bs1≢0; 0<bs1; 0≢bs1; _≟_;
      <-trans; <-irrefl; <-asym; ≮0; 0≤; ≤⇒≯; <⇒≱; >⇒≢; <⇒≢; 1≤|x|; 2^suc;
      *2≗2bin*; lexCompare;_=p_; lexBit-≈⇒≮; lexBit-<⇒≯; lexBit<-byPrefix; 
      lexBit<-bySuffix; <-≤-trans; ≤-<-trans; ≤-refl; ≤-reflexive; ≤-trans
     )
     renaming (lexBit<-irrefl to lex<-irrefl; lexBit<-asym to lex<-asym)

open import Bin2 using 
     (addC1; ++assoc; fromBits-bs:1; toBits∘fromBits; hasLast1-++; HasLast1; 
      hasLast1-bs:1; bs=1→hasLast1-1bs; predList<zeroes++<1:bs:1>>; fromℕ; 
      toℕ-x≡0⇒x≡0; predList<0:zeroes:1>; toℕ∘fromℕ; fromℕ∘toℕ; toℕ-pred-homo; 
      toℕ+homo; fromℕ+homo; toℕ-suc-homo; fromℕ-suc-homo; 0<toℕ-bs1; 
      pred-as-predN; 0+; +0; +-comm; suc∘pred-for>0; suc-even1 
     ) 
open import Bin3 using (toℕ*homo; fromℕ*homo; *-comm; rDistrib; *1; *2≗*2bin;
                                  *2≗+; *2-distrib; 2^-homo; toℕ-2^-homo)
 



--****************************************************************************
-- 1) The monotonicity laws for  _+_, _*_, _pred_, toℕ, fromℕ.
-- 2) The cancellation laws for  _+_.


open Bin

open Membership bitSetoid using (_∈_)
open Any

------------------------------------------------------------------------------
pred-1bs1 :  ∀ bs → pred ((1b ∷ bs) 1#) ≡ (0b ∷ bs) 1#
pred-1bs1 bs =  
    begin≡
      pred ((1b ∷ bs) 1#)                    ≡⟨ refl ⟩
      fromBits (predList ((1b ∷ bs) ∷ʳ 1b))  
                                   ≡⟨ cong fromBits 
                                        (predList<zeroes++<1:bs:1>> [] bs []a) 
                                    ⟩
      fromBits ((0b ∷ bs) ∷ʳ 1b)   ≡⟨ fromBits-bs:1 (0b ∷ bs) ⟩
      (0b ∷ bs) 1#
    end≡

private ∣_∣ : Bin → ℕ 
        ∣_∣ = bitLength 

1∈bs⇒|pred-bs1|≡1+|bs| :  ∀ bs → 1b ∈ bs → ∣ pred (bs 1#) ∣ ≡  1+ (ln bs)
1∈bs⇒|pred-bs1|≡1+|bs| bs 1∈bs =  
  let
    any-1-bs : Any (_≡b 1b) bs
    any-1-bs = Data.List.Any.map sym 1∈bs

    P = (_≡b 1b);   ¬P   = (_≢b 1b);         P? = (_≟b 1b)
    Q = (_≡b 0b);   ¬P⊆Q = \{b} → ≢1b⇒≡0b b

    (found′ pref b suff ¬P-pref b≡1b pref++b:suff≡bs) = 
                                              findExisting Bit P? bs any-1-bs
    pref=0 :  All (_≡b 0b) pref
    pref=0 =  Data.List.All.map ¬P⊆Q ¬P-pref 

    |pref| = ln pref;  |suff| = ln suff  

    map-1-pref = map const-1b pref

    hl1-units++0:suff:1 :  HasLast1 (map-1-pref ++ (0b ∷ (suff ∷ʳ 1b)))
    hl1-units++0:suff:1 = 
                        hasLast1-++ map-1-pref (0b ∷ (suff ∷ʳ 1b)) 
                                               (hasLast1-bs:1 (0b ∷ suff))
  in
  begin≡
    ∣ pred (bs 1#) ∣                        ≡⟨ refl ⟩
    ∣ fromBits (predList (bs ∷ʳ 1b)) ∣   
                              ≡⟨ cong (\x → ∣ fromBits (predList (x ∷ʳ 1b)) ∣)
                                      (sym pref++b:suff≡bs) 
                               ⟩
    ∣ fromBits (predList ((pref ++ (b ∷ suff)) ∷ʳ 1b)) ∣
                                      ≡⟨ cong (∣_∣ ∘ fromBits ∘ predList)
                                              (++assoc pref (b ∷ suff) [ 1b ])
                                       ⟩
    ∣ fromBits (predList (pref ++ ((b ∷ (suff ∷ʳ 1b))))) ∣
                         ≡⟨ cong (\x → ∣ fromBits (predList 
                                           (pref ++ ((x ∷ (suff ∷ʳ 1b))))) ∣ )
                                 b≡1b
                          ⟩
    ∣ fromBits (predList (pref ++ ((1b ∷ (suff ∷ʳ 1b))))) ∣
                            ≡⟨ cong (∣_∣ ∘ fromBits) 
                                 (predList<zeroes++<1:bs:1>> pref suff pref=0)
                             ⟩                          
    ∣ fromBits (map-1-pref ++ (0b ∷ (suff ∷ʳ 1b))) ∣       ≡⟨ refl ⟩
    ln (toBits (fromBits (map-1-pref ++ (0b ∷ (suff ∷ʳ 1b)))))
                 ≡⟨ cong ln
                       (toBits∘fromBits (map-1-pref ++ (0b ∷ (suff ∷ʳ 1b)))
                                                          hl1-units++0:suff:1)
                  ⟩
    ln (map-1-pref ++ (0b ∷ (suff ∷ʳ 1b)))         ≡⟨ length-++ map-1-pref ⟩
    ln map-1-pref +n (ln (0b ∷ (suff ∷ʳ 1b)))
                                      ≡⟨ cong (_+n (ln (0b ∷ (suff ∷ʳ 1b))))
                                              (length-map const-1b pref) 
                                       ⟩
    |pref| +n (1+ ln (suff ∷ʳ 1b))    ≡⟨ cong ((|pref| +n_) ∘ 1+_) 
                                              (length-xs:x 1b suff) 
                                       ⟩
    |pref| +n (1+ (1+ |suff|))        ≡⟨ sym (+n-assoc |pref| 1 (1+ |suff|)) ⟩
    (|pref| +n 1) +n (1+ |suff|)      ≡⟨ cong (_+n (1+ |suff|))
                                                   (+n-comm |pref| 1) ⟩
    1+ (|pref| +n (1+ |suff|))        ≡⟨ refl ⟩
    1+ (|pref| +n (ln (b ∷ suff)))    ≡⟨ cong 1+_ (sym (length-++ pref)) ⟩
    1+ (ln (pref ++ (b ∷ suff)))      ≡⟨ cong (1+_ ∘ ln) pref++b:suff≡bs ⟩
    1 +n (ln bs)
  end≡


------------------------------------------------------------------------------
all-0-bs⇒|pred-0bs1|≡1+|bs| :  ∀ bs → All (_≡b 0b) bs →
                                         ∣ pred ((0b ∷ bs) 1#) ∣ ≡  1+ (ln bs)
all-0-bs⇒|pred-0bs1|≡1+|bs| bs all-0-bs = 
  begin≡
    ∣ pred ((0b ∷ bs) 1#) ∣                       ≡⟨ refl ⟩
    ∣ fromBits (predList ((0b ∷ bs) ∷ʳ 1b)) ∣ 
                                       ≡⟨ cong (∣_∣ ∘ fromBits)
                                            (predList<0:zeroes:1> bs all-0-bs)
                                        ⟩
    ∣ fromBits (1b ∷ map-1-bs) ∣       ≡⟨ refl ⟩
    ln (toBits (fromBits (1b ∷ map-1-bs)))   
                                   ≡⟨ cong ln (toBits∘fromBits (1b ∷ map-1-bs)
                                                             hl1-1:map-1-bs) ⟩
    ln (1b ∷ map-1-bs)             ≡⟨ refl ⟩
    1+ (ln map-1-bs)               ≡⟨ cong 1+_ (length-map const-1b bs) ⟩
    1+ (ln bs)
  end≡
  where
  map-1-bs = map const-1b bs

  all-1-map-1-bs :  All (_≡b 1b) map-1-bs
  all-1-map-1-bs =  all-map-const 1b bs

  hl1-1:map-1-bs :  HasLast1 (1b ∷ map-1-bs)
  hl1-1:map-1-bs =  bs=1→hasLast1-1bs map-1-bs all-1-map-1-bs 


------------------------------------------------------------------------------
private 
  |pred-b:bs1|-as-⊎ : ∀ b bs → let |pred-a| = ∣ pred ((b ∷ bs) 1#) ∣
                               in
                               |pred-a| ≡ 2 +n ln bs  ⊎  |pred-a| ≡ 1+ (ln bs) 
  |pred-b:bs1|-as-⊎ ⊥b 
  |pred-b:bs1|-as-⊎ 1b bs =  
                          inj₁ (1∈bs⇒|pred-bs1|≡1+|bs| (1b ∷ bs) (here refl))

  |pred-b:bs1|-as-⊎ 0b bs   with all (_≟b 0b) bs 

  ... | yes all-0-bs =  inj₂ (all-0-bs⇒|pred-0bs1|≡1+|bs| bs all-0-bs) 
  ... | no ¬all-0-bs =  inj₁ (1∈bs⇒|pred-bs1|≡1+|bs| (0b ∷ bs) (there 1∈bs))
                        where
                        any-¬0 : Any (_≢b 0b) bs 
                        any-¬0 = ¬All⇒Any¬ (_≟b 0b) bs ¬all-0-bs

                        any-1 = Data.List.Any.map (\{b} → ≢0b⇒≡1b b) any-¬0   
                        1∈bs  = Data.List.Any.map sym any-1

------------------------------------------------------------------------------
|pred|-as-⊎ :  (x : Bin) →  (∣ pred x ∣ ≡ ∣ x ∣) ⊎ (∣ pred x ∣ ≡ predN ∣ x ∣)
|pred|-as-⊎ 0#            =  inj₁ refl
|pred|-as-⊎ ([] 1#)       =  inj₁ refl
|pred|-as-⊎ ((b ∷ bs) 1#) with |pred-b:bs1|-as-⊎ b bs
...
    | inj₁ |pred-x|≡2+|bs| = 
            inj₁ 
              (begin≡ ∣ pred x ∣         ≡⟨ |pred-x|≡2+|bs| ⟩
                      1+ (ln (b ∷ bs))   ≡⟨ sym (length-xs:x 1b (b ∷ bs)) ⟩
                      ∣ x ∣
               end≡
              ) 
              where  x = (b ∷ bs) 1#
                                           
... | inj₂ |pred-x|≡1+|bs| = 
        inj₂ 
          (begin≡ ∣ pred x ∣             ≡⟨ |pred-x|≡1+|bs| ⟩
                  1+ (ln bs)             ≡⟨ refl ⟩
                  predN (2 +n (ln bs))   ≡⟨ cong predN 
                                             (sym (length-xs:x 1b (b ∷ bs))) ⟩
                  predN ∣ x ∣
           end≡
          ) 
          where  x = (b ∷ bs) 1#                       

-------------------------------------------------------
|x|-1≤|pred-x| :  (x : Bin) → predN ∣ x ∣ ≤n ∣ pred x ∣
|x|-1≤|pred-x| x =  
  case 
      |pred|-as-⊎ x 
  of \ 
  { (inj₁ |pred-x|≡|x|) →  ≤nBegin predN (∣ x ∣)   ≤n[ pred-n≤n (∣ x ∣) ]
                                   ∣ x ∣          ≡≤n[ sym |pred-x|≡|x| ]
                                   ∣ pred x ∣
                           ≤nEnd

  ; (inj₂ |pred-x|≡pred-|x|) → ≤n-reflexive (sym |pred-x|≡pred-|x|)
  }



------------------------------------------------------------------------------
open Tri

toℕ-x<2^|x| :  ∀ x →  toℕ x <n 2 ^ ∣ x ∣

toℕ-x<2^|x| 0#            =  s≤s z≤n
toℕ-x<2^|x| ([] 1#)       =  ≤n-refl
toℕ-x<2^|x| ((b ∷ bs) 1#) = 
  ≤nBegin
    1 +n (bN +n bs1N *n 2)     ≡≤n[ sym (+n-assoc 1 bN (bs1N *n 2)) ]
    (1 +n bN) +n (bs1N *n 2)    ≤n[ NatP.+-mono-≤ 1+bN≤2 
                                                    (≤n-refl {bs1N *n 2}) ]
    2 +n (bs1N *n 2)           ≡≤n[ refl ]
    (1+ toℕ (bs 1#)) *n 2       ≤n[ NatP.*-mono-≤ rec ≤n-refl ]
    (2 ^ ∣ bs 1# ∣) *n 2       ≡≤n[ NatP.*-comm (2 ^ ∣ bs 1# ∣) 2 ]
    2 *n (2 ^ ∣ bs 1# ∣)       ≡≤n[ refl ]
    2 ^ ∣ (b ∷ bs) 1# ∣ 
  ≤nEnd
  where
  bs1N   = toℕ (bs 1#)
  bN     = Fin.toℕ b
  bN≤1   = FinP.prop-toℕ-≤ {2} b 
  1+bN≤2 = NatP.+-mono-≤ (≤n-refl {1}) bN≤1

  rec :  1+ (toℕ (bs 1#))  ≤n  2 ^ ∣ bs 1# ∣
  rec =  toℕ-x<2^|x| (bs 1#) 


2^|bs|≤toℕ-bs1 :  ∀ bs →  2 ^ (ln bs) ≤n toℕ (bs 1#) 
2^|bs|≤toℕ-bs1 []       =  ≤n-refl
2^|bs|≤toℕ-bs1 (b ∷ bs) =  goal
  where
  bN   = Fin.toℕ b
  bs1N = toℕ (bs 1#)

  rec :  2 ^ (ln bs) ≤n bs1N
  rec =  2^|bs|≤toℕ-bs1 bs

  goal :  2 ^ (1+ ln bs)  ≤n  toℕ ((b ∷ bs) 1#) 
  goal = 
   ≤nBegin 
    2 ^ (1+ ln bs)             ≡≤n[ refl ]  
    2 *n (2 ^ (ln bs))          ≤n[ NatP.*-mono-≤ (≤n-refl {2}) rec ]  
    2 *n (toℕ (bs 1#))         ≡≤n[ NatP.*-comm 2 bs1N ]  
    bs1N *n 2                   ≤n[ NatP.n≤m+n bN (bs1N *n 2) ]  
    bN +n (toℕ (bs 1#)) *n 2   ≡≤n[ refl ]  
    toℕ ((b ∷ bs) 1#) 
   ≤nEnd 


--------------------------------------------------------------
|x|<|y|⇒toN-x<toN-y :  ∀ x y → ∣ x ∣ <n ∣ y ∣ → toℕ x <n toℕ y  

|x|<|y|⇒toN-x<toN-y x 0#      |x|<1     =  
                                         ⊥-elim (NatProp0.≤⇒≯ (1≤|x| x) |x|<1)
|x|<|y|⇒toN-x<toN-y x (bs 1#) |x|<|bs1| =
  ≤nBegin
    1+ (toℕ x)                 ≤n[ toℕ-x<2^|x| x ] 
    2 ^ ∣ x ∣                  ≤n[ 2^-mono-≤ |x|≤pred|bs1| ]  
    2 ^ (predN ∣ bs 1# ∣)     ≡≤n[ cong ((2 ^_) ∘ predN) (length-xs:x 1b bs) ]
    2 ^ (predN (1+ ln bs))    ≡≤n[ refl ]
    2 ^ (ln bs)                ≤n[ 2^|bs|≤toℕ-bs1 bs ] 
    toℕ (bs 1#)
  ≤nEnd
  where
  |x|≤pred|bs1| :  ∣ x ∣ ≤n predN ∣ bs 1# ∣
  |x|≤pred|bs1| =  predN-mono |x|<|bs1|

------------------------------------------------------------------------------
open Pointwise using () renaming ([] to []p; _∷_ to _∷p_)

=p-refl :  Reflexive _=p_ 
=p-refl =  Pointwise.refl (refl {A = Bit}) 

=p-sym :  Symmetric _=p_ 
=p-sym =  Pointwise.symmetric (sym {A = Bit}) 

module SLexBit = StrictLex
open SLexBit using (this; next)


------------------------------------------------------------------------------
toℕ-mono-forEqualLength :  
                 ∀ bs bs' → ln bs ≡ ln bs' → lex< (rev bs) (rev bs') → 
                                                   toℕ (bs 1#) <n toℕ (bs' 1#)

toℕ-mono-forEqualLength [] [] _ []<[] =  ⊥-elim ([]≮[] []<[])
                                         where
                                         []=p=[] :  Pointwise.Rel _≡_ [] []
                                         []=p=[] =  Pointwise.≡⇒Rel≡ refl

                                         []≮[] = lex<-irrefl []=p=[]
toℕ-mono-forEqualLength [] (_ ∷ _) ()
toℕ-mono-forEqualLength (_ ∷ _)    [] ()
toℕ-mono-forEqualLength (b ∷ bs) (b' ∷ bs') |bbs|≡|b'bs'| rbbs<rb'bs' = 
                                                     aux (lexCompare rbs rbs')
  where
  bN   = Fin.toℕ {2} b;     b'N    = Fin.toℕ {2} b'
  bs1  = bs 1#;             bs'1   = bs' 1#
  bs1N = toℕ bs1;           bs'1N  = toℕ bs'1 
  rbs  = rev bs;            rbs'   = rev bs'   
  rbbs = rev (b ∷ bs);      rb'bs' = rev (b' ∷ bs')

  |bs|≡|bs'|   = cong predN |bbs|≡|b'bs'| 
  |rbs|≡|rbs'| = begin≡ 
                   ln (rev bs)    ≡⟨ length-reverse bs ⟩
                   ln bs          ≡⟨ |bs|≡|bs'| ⟩
                   ln bs'         ≡⟨ sym (length-reverse bs') ⟩
                   ln (rev bs')
                 end≡ 

  rbbs≡rbs:b : rbbs ≡ rbs ∷ʳ b
  rbbs≡rbs:b = reverse-++-commute [ b ] bs

  rb'bs'≡rbs':b' = reverse-++-commute [ b' ] bs'
  rbs':b'≡rb'bs' = sym rb'bs'≡rbs':b'
  rbs:b≡rbbs     = sym rbbs≡rbs:b 

  ----------------------------------------------------------------------------
  aux : Tri (lex< rbs rbs') (Pointwise.Rel _≡_ rbs rbs') (lex< rbs' rbs) →  
                                       bN +n bs1N *n 2  <n  b'N +n bs'1N *n 2 
  aux (tri< rbs<rbs' _ _) =  
    ≤nBegin
      1+  (bN +n bs1N *n 2)            ≡≤n[ +n-comm 1 (bN +n bs1N *n 2) ]
      (bN +n bs1N *n 2) +n 1           ≡≤n[ +n-assoc bN (bs1N *n 2) 1 ]
      bN +n (bs1N *n 2 +n 1)            ≤n[ +n-mono-≤ bN≤1+b'N ≤n-refl ]
      (1+ b'N) +n (bs1N *n 2 +n 1)     ≡≤n[ cong (_+n (bs1N *n 2 +n 1)) 
                                                             (+n-comm 1 b'N) ]
      (b'N +n 1) +n (bs1N *n 2 +n 1)   ≡≤n[ +n-assoc b'N 1 (bs1N *n 2 +n 1) ]
      b'N +n (1+ (bs1N *n 2 +n 1))     ≡≤n[ cong ((b'N +n_) ∘ 1+_) 
                                                 (+n-comm (bs1N *n 2) 1) ]
      b'N +n (2 +n (bs1N *n 2))        ≡≤n[ cong 
                                              (\x → b'N +n (x +n (bs1N *n 2)))
                                              (sym (NatProp0.1* 2))
                                          ]
      b'N  +n (1 *n 2 +n bs1N *n 2)    ≡≤n[ cong (b'N +n_)
                                                 (*n-rDistrib 2 1 bs1N) ] 
      b'N  +n (1+ bs1N) *n 2            ≤n[ +n-mono-≤ (≤n-refl {b'N}) leq ]
      b'N  +n bs'1N *n 2 
    ≤nEnd
    where
    bN≤1+b'N =  ≤nBegin bN        ≤n[ FinP.prop-toℕ-≤ {2} b ]
                        1         ≤n[ m≤m+n 1 b'N ]
                        1+ b'N
                ≤nEnd

    bs1N<bs'1N :  toℕ (bs 1#) <n toℕ (bs' 1#) 
    bs1N<bs'1N =  toℕ-mono-forEqualLength bs bs' |bs|≡|bs'| rbs<rbs'

    leq :  (1+ bs1N) *n 2  ≤n  bs'1N *n 2 
    leq =  *n-mono-≤ bs1N<bs'1N (≤n-refl {2})

  aux (tri≈ _ rbs=p=rbs' _) =  aux' (FinP.cmp {2} b b')
    where
    rbs≡rbs' : rbs ≡ rbs'
    rbs≡rbs' = Pointwise.Rel≡⇒≡ rbs=p=rbs'

    bs≡bs' : bs ≡ bs' 
    bs≡bs' = reverse-injective-≡ rbs≡rbs'

    aux' : Tri (b bit< b') (b ≡b b') (b' bit< b) → 
                                     bN +n bs1N *n 2  <n  b'N +n bs'1N *n 2
    aux' (tri< b<b' _ _) = 
      ≤nBegin
       1+ (bN +n bs1N *n 2)    ≡≤n[ cong (\x → 1+ (bN +n x *n 2)) bs1N≡bs'1N ]
       (1+ bN) +n bs'1N *n 2    ≤n[ +n-mono-≤ b<b' (≤n-refl {bs'1N *n 2}) ]
       b'N +n bs'1N *n 2 
      ≤nEnd
      where  bs1N≡bs'1N = cong (toℕ ∘ _1#) bs≡bs'

    aux' (tri≈ _ b≡b' _) =  ⊥-elim (rbbs≮rb'bs' rbbs<rb'bs')
                            where
                            bbs≡b'bs'     = cong₂ _∷_ b≡b' bs≡bs'
                            rbbs≡rb'bs'   = cong rev bbs≡b'bs'
                            rbbs=p=rb'bs' = Pointwise.≡⇒Rel≡ rbbs≡rb'bs'
                            rbbs≮rb'bs'   = lexBit-≈⇒≮ rbbs=p=rb'bs' 
                        
    aux' (tri> _ _ b'<b) =  ⊥-elim (rbbs≮rb'bs' rbbs<rb'bs')
         where
         rbs':b'<rbs:b :  lex< (rbs' ∷ʳ b') (rbs ∷ʳ b)   
         rbs':b'<rbs:b =  proj₁ (lexBit<-bySuffix rbs' [ b' ] rbs [ b ]
                                              (=p-sym rbs=p=rbs')) (this b'<b) 

         rb'bs'<rbbs =  subst₂ lex< rbs':b'≡rb'bs' rbs:b≡rbbs rbs':b'<rbs:b
         rbbs≮rb'bs' =  lex<-asym rb'bs'<rbbs

  aux (tri> _ _ rbs'<rbs) =  ⊥-elim (rbbs≮rb'bs' rbbs<rb'bs')
      where
      rbs':b'<rbs:b :  lex< (rbs' ∷ʳ b') (rbs ∷ʳ b)   
      rbs':b'<rbs:b =  lexBit<-byPrefix rbs' rbs (sym |rbs|≡|rbs'|) rbs'<rbs 

      rb'bs'<rbbs :  lex< (rev (b' ∷ bs')) (rev (b ∷ bs)) 
      rb'bs'<rbbs =  subst₂ lex< rbs':b'≡rb'bs' rbs:b≡rbbs rbs':b'<rbs:b  

      rbbs≮rb'bs' =  lexBit-<⇒≯ rb'bs'<rbbs 


------------------------------------------------------------------------------
toℕ-mono-< :  toℕ Preserves _<_ ⟶ _<n_

toℕ-mono-< {x}  {y}  (inj₁ |x|<|y|)         =  |x|<|y|⇒toN-x<toN-y x y |x|<|y|
toℕ-mono-< {0#} {0#} (inj₂ (_ , (this ()))) 
toℕ-mono-< {0#} {0#} (inj₂ (_ , (next _ []<[]))) =  
                                            ⊥-elim (lex<-irrefl =p-refl []<[])
toℕ-mono-< {0#} {[] 1#}      (inj₂ _) =  s≤s z≤n
toℕ-mono-< {0#} {(b ∷ bs) 1#} _       =  
                                    |x|<|y|⇒toN-x<toN-y 0# ((b ∷ bs) 1#) 1<|y| 
                      where
                      y = (b ∷ bs) 1#

                      |y|≡2+|bs| :  ∣ y ∣ ≡ 2 +n (ln bs) 
                      |y|≡2+|bs| =  cong 1+_ (length-xs:x 1b bs)
                              
                      1<|y| =  ≤nBegin 2              ≤n[ m≤m+n 2 (ln bs) ]
                                       2 +n (ln bs)  ≡≤n[ sym |y|≡2+|bs| ]
                                       ∣ y ∣ 
                               ≤nEnd

toℕ-mono-< {bs 1#} {0#}     bs1<0 =  ⊥-elim (<-asym {0#} {bs 1#} (0<bs1 bs) 
                                                                        bs1<0)
toℕ-mono-< {bs 1#} {bs' 1#} (inj₂ (|bs1|≡|bs'1| , rbs1<rbs'1)) = 

                            toℕ-mono-forEqualLength bs bs' |bs|≡|bs'| rbs<rbs'
        where 
        rbs = rev bs;   rbs' = rev bs'   

        |bs|≡|bs'| =  
           begin≡ ln bs                   ≡⟨ cong predN 
                                                  (sym (length-xs:x 1b bs)) ⟩
                  predN (ln (bs ∷ʳ 1b))   ≡⟨ cong predN |bs1|≡|bs'1| ⟩
                  predN (ln (bs' ∷ʳ 1b))  ≡⟨ cong predN (length-xs:x 1b bs') ⟩
                  ln bs'
           end≡

        rbs1≡1rbs :  rev (bs ∷ʳ 1b) ≡ 1b ∷ (rev bs)
        rbs1≡1rbs =  reverse-++-commute bs [ 1b ]

        rbs'1≡1rbs' =  reverse-++-commute bs' [ 1b ]

        1rbs<1rbs' : lex< (1b ∷ rbs) (1b ∷ rbs')
        1rbs<1rbs' = subst₂ lex< rbs1≡1rbs rbs'1≡1rbs' rbs1<rbs'1

        rbs<rbs' : lex< rbs rbs'
        rbs<rbs' = proj₂ (lexBit<-bySuffix [ 1b ] rbs [ 1b ] rbs' 
                                                  (refl ∷p []p)) 1rbs<1rbs'

------------------------------------------------------------------------------
toℕ-mono-≤ :  toℕ Preserves _≤_ ⟶ _≤n_

toℕ-mono-≤ {x} {y} (inj₁ x<y) =  NatP.<⇒≤ (toℕ-mono-< {x} {y} x<y)
toℕ-mono-≤ {x} {y} (inj₂ x≡y) =  NatP.≤-reflexive (cong toℕ x≡y)

------------------------------------------------------------------------------
fromℕ-mono-< :  fromℕ Preserves _<n_ ⟶ _<_
fromℕ-mono-< {m} {n} m<n = 
      let 
        x = fromℕ m;  y = fromℕ n
      in
      case <-cmp x y
      of \ 
      { (tri< x<y _   _ ) → x<y
      ; (tri≈ _   x≡y _ ) → let m≡n = begin≡ m       ≡⟨ sym (toℕ∘fromℕ m) ⟩
                                             toℕ x   ≡⟨ cong toℕ x≡y ⟩
                                             toℕ y   ≡⟨ toℕ∘fromℕ n ⟩
                                             n
                                      end≡
                            in
                            ⊥-elim (NatProp0.≡⇒≮ m≡n m<n)
 
      ; (tri> _   _  y<x) → let yN<xN = toℕ-mono-< {y} {x} y<x
                                xN≡m  = toℕ∘fromℕ m
                                yN≡n  = toℕ∘fromℕ n
                                n<m   = subst₂ _<n_ yN≡n xN≡m yN<xN
                            in  
                            ⊥-elim (<n-asym n<m m<n)
      }


fromℕ-mono-≤ :  fromℕ Preserves _≤n_ ⟶ _≤_
fromℕ-mono-≤ m≤n =
                 case NatProp0.≤⇒⊎ m≤n of \ 
                                       { (inj₁ m<n) → inj₁ (fromℕ-mono-< m<n)
                                       ; (inj₂ m≡n) → inj₂ (cong fromℕ m≡n)
                                       }

------------------------------------------------------------------------------
pred-mono-< :  ∀ bs y → bs 1# < y → pred (bs 1#) < pred y
pred-mono-< bs y bs1<y = 
                       subst₂ _<_ (sym pbs1≡fromN-pbs1N) (sym py≡fromN-pyN) le
            where
            bs1 = bs 1#;   bs1N = toℕ bs1;  yN = toℕ y

            bs1N<yN = toℕ-mono-< {bs1} {y}   bs1<y
            0<bs1N  = toℕ-mono-< {0#}  {bs1} (0<bs1 bs)

            pbs1N<pyN :  predN bs1N <n predN yN  
            pbs1N<pyN =  NatProp0.pred-mono-< 0<bs1N bs1N<yN

            pbs1≡fromN-pbs1N = pred-as-predN (bs 1#)
            py≡fromN-pyN     = pred-as-predN y

            le :  fromℕ (predN bs1N) < fromℕ (predN yN)
            le =  fromℕ-mono-< pbs1N<pyN 


pred-mono-≤ :  pred Preserves _≤_ ⟶ _≤_

pred-mono-≤ {_}     {_} (inj₂ x≡y) =  inj₂ (cong pred x≡y)
pred-mono-≤ {0#}    {y} _          =  0≤ (pred y)  
pred-mono-≤ {bs 1#} {y} (inj₁ x<y) =  inj₁ (pred-mono-< bs y x<y) 


------------------------------------------------------------------------------
open InequalityReasoning {A = Bin} _<_ _≤_ 
                                   (\{x y}   → ≤-reflexive {x} {y})
                                   (\{x y z} → <-trans {x} {y} {z})
                                   (\{x y z} → ≤-trans {x} {y} {z})
                                   (\{x y z} → <-≤-trans {x} {y} {z})
                                   (\{x y z} → ≤-<-trans {x} {y} {z})
{-
module InequalityReasoning {a b} {A : Set a}
              (_<_ : A → A → Set b)
              (_≤_ : A → A → Set b)
              (leq-refl     : ∀ {x y}   → x ≡ y → x ≤ y)
              (lt-trans     : ∀ {x y z} → x < y → y < z → x < z)
              (leq-trans    : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
              (lt/leq-trans : ∀ {x y z} → x < y → y ≤ z → x < z)
              (leq/lt-trans : ∀ {x y z} → x ≤ y → y < z → x < z)
 

-}


+-mono-≤ :  _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_

+-mono-≤ {x} {x'} {y} {y'} x≤x' y≤y' =    
  begin  
    x + y                   ≡[ cong₂ _+_ (sym (fromℕ∘toℕ x)) 
                                         (sym (fromℕ∘toℕ y)) ] 
    fromℕ xN + fromℕ yN     ≡[ sym (fromℕ+homo xN yN) ] 
    fromℕ (xN +n yN)        ≤[ fromℕ-mono-≤ (+n-mono-≤ xN≤x'N yN≤y'N) ] 
    fromℕ (x'N +n y'N)      ≡[ fromℕ+homo x'N y'N ] 
    fromℕ x'N + fromℕ y'N   ≡[ cong₂ _+_ (fromℕ∘toℕ x') (fromℕ∘toℕ y') ] 
    x' + y'
  ∎ 
  where
  xN     = toℕ x;             yN     = toℕ y
  x'N    = toℕ x';            y'N    = toℕ y'
  xN≤x'N = toℕ-mono-≤ x≤x';   yN≤y'N = toℕ-mono-≤ y≤y'   

--------------------------------------------
+-mono-<-≤ :  _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_

+-mono-<-≤ {x} {x'} {y} {y'} x<x' y≤y' =  
                             subst₂ _<_ 
                                 (fromℕ∘toℕ (x + y)) (fromℕ∘toℕ (x' + y')) le
  where
  xN     = toℕ x;                      yN     = toℕ y
  x'N    = toℕ x';                     y'N    = toℕ y'
  xN<x'N = toℕ-mono-< {x} {x'} x<x';   yN≤y'N = toℕ-mono-≤ {y} {y'} y≤y'   

  toℕ[x+y]<toℕ[x'+y'] :  toℕ (x + y) <n toℕ (x' + y')
  toℕ[x+y]<toℕ[x'+y'] =
    ≤nBegin
      1+ (toℕ (x + y))    ≡≤n[ cong 1+_ (toℕ+homo x y) ]
      (1+ xN) +n yN        ≤n[ +n-mono-≤ xN<x'N yN≤y'N ]
      x'N +n y'N          ≡≤n[ sym (toℕ+homo x' y') ]
      toℕ (x' + y')
    ≤nEnd

  fromℕ[xN+yN]<fromℕ[x'N+y'N] = fromℕ-mono-< toℕ[x+y]<toℕ[x'+y']

  le :  fromℕ (toℕ (x + y)) < fromℕ (toℕ (x' + y')) 
  le =  fromℕ-mono-< toℕ[x+y]<toℕ[x'+y']


--------------------------------------------
+-mono-≤-< :  _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_

+-mono-≤-< {x} {x'} {y} {y'} x≤x' y<y' =
                        subst₂ _<_ (+-comm y x) (+-comm y' x') y+x<y'+x'
                        where
                        y+x<y'+x' =  +-mono-<-≤ {y} {y'} {x} {x'} y<y' x≤x'

suc-mono-≤ :  suc Preserves _≤_ ⟶ _≤_
suc-mono-≤ =
           +-mono-≤ (≤-refl {1'}) -- (≤-reflexive {1'})

suc-mono-< :  suc Preserves _<_ ⟶ _<_
suc-mono-< {x} {y} =
                   +-mono-≤-< {1'} {1'} {x} {y} (≤-refl {1'})

pred-bs1< :  ∀ bs → pred (bs 1#) < bs 1#
pred-bs1< bs = 
          begin pred a                 ≡[ sym (fromℕ∘toℕ (pred a)) ]
                fromℕ (toℕ (pred a))   ≡[ cong fromℕ (toℕ-pred-homo a) ]
                fromℕ (predN aN)       <[ fromℕ-mono-< (NatProp0.pred< 0<aN) ]
                fromℕ aN               ≡[ fromℕ∘toℕ a ]
                a
          ∎
          where
          a = bs 1#;   aN = toℕ a;   0<aN = toℕ-mono-< {0#} {a} (0<bs1 bs)


pred< :  ∀ {x} → x ≢ 0# → pred x < x

pred< {bs 1#} _   =  pred-bs1< bs
pred< {0#}    0≢0 =  ⊥-elim (0≢0 refl) 


x≤x+y :  (x y : Bin) → x ≤ x + y
x≤x+y x y =
          begin x        ≡[ sym (+0 x) ]
                x + 0#   ≤[ +-mono-≤ (≤-refl {x}) (0≤ y) ]
                x + y
          ∎ 

x≤y+x :  (x y : Bin) → x ≤ y + x
x≤y+x x y =
          subst (x ≤_) (+-comm x y) (x≤x+y x y)

x<1+x :  ∀ x → x < suc x
x<1+x x =
        subst (_< (1' + x)) (0+ x) 0+x<1+x
        where
        0+x<1+x =  +-mono-<-≤ {0#} {1'} {_} {_} (0<bs1 []) (≤-refl {x})

x<x+1 :  ∀ x → x < x + 1'
x<x+1 x =
        subst (x <_) (+-comm 1' x) (x<1+x x)

0<1+x :  ∀ x → 0# < suc x 
0<1+x x =  
        +-mono-<-≤ {0#} {1'} {_} {_} (0<bs1 []) (0≤ x) 

0≢1+x :  ∀ x → 0# ≢ suc x 
0≢1+x =  
      <⇒≢ ∘ 0<1+x 

------------------------------------------
<-iff-suc≤ :  ∀ {x y} → x < y ←→ suc x ≤ y
<-iff-suc≤ {x} {y} =  
                   (to , from)
  where
  xN = toℕ x;  yN = toℕ y

  to :  x < y → suc x ≤ y
  to x<y = 
         begin suc x                 ≡[ sym (fromℕ∘toℕ (suc x)) ] 
               fromℕ (toℕ (suc x))   ≡[ cong fromℕ (toℕ+homo 1' x) ]
               fromℕ (1+ xN)         ≤[ fromℕ-mono-≤ {1+ xN} {yN} xN<yN ]
               fromℕ yN              ≡[ fromℕ∘toℕ y ] 
               y
         ∎
         where xN<yN = toℕ-mono-< {x} {y} x<y
         
  from :  suc x ≤ y → x < y
  from suc-x≤y =  
               begin x           ≡[ sym (fromℕ∘toℕ x) ] 
                     fromℕ xN    <[ fromℕ-mono-< xN<yN ]
                     fromℕ yN    ≡[ fromℕ∘toℕ y ] 
                     y
               ∎
               where
               xN<yN = ≤nBegin 1 +n xN      ≡≤n[ sym (toℕ+homo 1' x) ]
                               toℕ (suc x)   ≤n[ toℕ-mono-≤ suc-x≤y ]
                               yN
                       ≤nEnd
     
<⇒suc≤ :  ∀ {x y} → x < y → suc x ≤ y
<⇒suc≤ {x} {y} x<y =
                   proj₁ (<-iff-suc≤ {x} {y}) x<y 

suc≤⇒< :  ∀ {x y} → suc x ≤ y → x < y
suc≤⇒< {x} {y} x≤y =
                   proj₂ (<-iff-suc≤ {x} {y}) x≤y 

                    
--------------------------------------------
+-lCancel :  ∀ x y z → x + y ≡ x + z → y ≡ z     -- prove by applying toℕ
+-lCancel x y z x+y≡x+z =
                        begin≡ y          ≡⟨ sym (fromℕ∘toℕ y) ⟩
                               fromℕ yN   ≡⟨ cong fromℕ yN≡zN ⟩
                               fromℕ zN   ≡⟨ fromℕ∘toℕ z ⟩
                               z
                        end≡
       where
       xN = toℕ x;  yN = toℕ y;  zN = toℕ z

       eq = begin≡ xN +n yN      ≡⟨ sym (toℕ+homo x y) ⟩
                   toℕ (x + y)   ≡⟨ cong toℕ x+y≡x+z ⟩
                   toℕ (x + z)   ≡⟨ toℕ+homo x z ⟩
                   xN +n zN
            end≡

       yN≡zN = begin≡ yN                 ≡⟨ sym (m+n∸n≡m yN xN)⟩
                      (yN +n xN) ∸n xN   ≡⟨ cong (_∸n xN) (+n-comm yN xN) ⟩
                      (xN +n yN) ∸n xN   ≡⟨ cong (_∸n xN) eq ⟩
                      (xN +n zN) ∸n xN   ≡⟨ cong (_∸n xN) (+n-comm xN zN) ⟩
                      (zN +n xN) ∸n xN   ≡⟨ m+n∸n≡m zN xN ⟩
                      zN
               end≡

+-rCancel :  ∀ x y z → y + x ≡ z + x → y ≡ z
+-rCancel x y z y+x≡z+x =
                        +-lCancel x y z x+y≡x+z 
                        where
                        x+y≡x+z = begin≡ x + y   ≡⟨ +-comm x y ⟩
                                         y + x   ≡⟨ y+x≡z+x ⟩
                                         z + x   ≡⟨ +-comm z x ⟩
                                         x + z
                                  end≡      


------------------------------------------
*-mono-≤ :  _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_

*-mono-≤ {x} {x'} {y} {y'} x≤x' y≤y' =
  begin
    x * y                   ≡[ cong₂ _*_ (sym (fromℕ∘toℕ x))
                                         (sym (fromℕ∘toℕ y)) ]
    fromℕ xN * fromℕ yN     ≡[ sym (fromℕ*homo xN yN) ]
    fromℕ (xN *n yN)        ≤[ fromℕ-mono-≤ (*n-mono-≤ xN≤x'N yN≤y'N) ]
    fromℕ (x'N *n y'N)      ≡[ fromℕ*homo x'N y'N ]
    fromℕ x'N * fromℕ y'N   ≡[ cong₂ _*_ (fromℕ∘toℕ x') (fromℕ∘toℕ y') ]
    x' * y'
  ∎
  where
  xN     = toℕ x;             yN     = toℕ y
  x'N    = toℕ x';            y'N    = toℕ y'
  xN≤x'N = toℕ-mono-≤ x≤x';   yN≤y'N = toℕ-mono-≤ y≤y'

------------------------------------
*2-mono-≤ :  _*2 Preserves _≤_ ⟶ _≤_
*2-mono-≤ {x} {y} x≤y =
                      begin x *2     ≡[ *2≗*2bin x ]
                            x * 2'   ≤[ *-mono-≤ x≤y ≤-refl ]
                            y * 2'   ≡[ sym (*2≗*2bin y) ]
                            y *2
                      ∎

---------------------------------------------------
*-lMono-< :  ∀ x → (_* (suc x)) Preserves _<_ ⟶ _<_ 
*-lMono-< x {y} {z} y<z =
  begin 
    y * suc x                     ≡[ sym (fromℕ∘toℕ (y * suc x)) ]
    fromℕ (toℕ (y * suc x))       ≡[ cong fromℕ (toℕ*homo y (suc x)) ]
    fromℕ (yN *n (toℕ (suc x)))   ≡[ cong (fromℕ ∘ (yN *n_)) (toℕ-suc-homo x) 
                                   ]
    fromℕ (yN *n (1+ xN))         <[ fromℕ-mono-< 
                                         (NatP.*-monoˡ-< xN {yN} {zN} yN<zN) ]
    fromℕ (zN *n (1+ xN))         ≡[ fromℕ*homo zN (1+ xN) ]
    fromℕ zN * (fromℕ (1+ xN))    ≡[ cong₂ _*_ (fromℕ∘toℕ z) 
                                               (fromℕ-suc-homo xN) ]
    z * (suc (fromℕ xN))          ≡[ cong ((z *_) ∘ suc) (fromℕ∘toℕ x) ] 
    z * (suc x)  
  ∎ 
  where
  xN = toℕ x;   yN = toℕ y;   zN = toℕ z;   yN<zN = toℕ-mono-< {y} {z} y<z


*-rMono-< :  ∀ x → ((suc x) *_) Preserves _<_ ⟶ _<_ 
*-rMono-< x {y} {z} y<z =
                        begin suc x * y    ≡[ *-comm (suc x) y ]
                              y * suc x    <[ *-lMono-< x {y} {z} y<z ]
                              z * suc x    ≡[ *-comm z (suc x) ]
                              suc x * z
                        ∎

-----------------------
1≤2^ :  ∀ n → 1' ≤ 2^ n

1≤2^ 0      =  ≤-refl
1≤2^ (1+ n) =  begin 1'          ≤[ x≤x+y 1' 1' ]
                     2'          ≤[ *2-mono-≤ (1≤2^ n) ]
                     (2^ n) *2   ≡[ sym (2^suc n) ]
                     2^ (1+ n)
               ∎

0<2^ :  ∀ n → 0# < 2^ n
0<2^ n = 
       <-≤-trans {0#} {1'} {2^ n} (0<bs1 []) (1≤2^ n)

2^-mono-< :  2^_ Preserves _<n_ ⟶ _<_
2^-mono-< {m} {n} m<n =
              begin 2^ m                 ≡[ sym (*1 (2^ m)) ]
                    (2^ m) * 1'          ≡[ cong (_* 1') (sym suc-p2^m≡2^m) ]
                    (suc p2^m) * 1'      <[ *-rMono-< p2^m {1'} {2^ d} 1<2^d ]
                    (suc p2^m) * (2^ d)  ≡[ cong (_* (2^ d)) suc-p2^m≡2^m ]
                    (2^ m) * (2^ d)      ≡[ sym (2^-homo m d) ]
                    2^ (m +n d)          ≡[ cong 2^_ m+d≡n ]
                    2^ n
              ∎
              where
              d      = n ∸n m
              0<d    = m<n⇒0<n∸m m<n 
              pd     = predN d
              1+pd≡d = NatProp0.suc∘pred 0<d 
              m+d≡n  = m+n∸m≡n (NatP.<⇒≤ m<n)
              p2^m   = pred (2^ m)

              suc-p2^m≡2^m : suc p2^m ≡ 2^ m
              suc-p2^m≡2^m = suc∘pred-for>0 (0<2^ m)

              1<2^d :  1' < 2^ d  
              1<2^d =  begin 1'            <[ x<1+x 1' ]
                             2'            ≡[ sym (*1 2') ]
                             2' * 1'       ≤[ *-mono-≤ {2'} {_} {1'} {2^ pd} 
                                                       ≤-refl (1≤2^ pd) ]
                             2' * (2^ pd)  ≡[ sym (*2≗2bin* (2^ pd)) ]
                             (2^ pd) *2    ≡[ sym (2^suc pd) ]
                             2^ (1+ pd)    ≡[ cong 2^_ 1+pd≡d ]
                             2^ d
                       ∎

------------------------------------------------------------------------------
x<y⇒a+x*a≤y*a :  ∀ {x y} a → x < y → a + x * a ≤ y * a
x<y⇒a+x*a≤y*a {x} {y} a x<y =
                  subst₂ _≤_ (fromℕ∘toℕ (a + x * a)) (fromℕ∘toℕ (y * a)) le'
  where
  xN = toℕ x;  yN = toℕ y;  aN = toℕ a;  xN<yN = toℕ-mono-< {x} {y} x<y

  le :  toℕ (a + x * a) ≤n toℕ (y * a)
  le =  ≤nBegin
          toℕ (a + x * a)     ≡≤n[ toℕ+homo a (x * a) ]
          aN +n toℕ (x * a)   ≡≤n[ cong (aN +n_) (toℕ*homo x a) ]
          aN +n (xN *n aN)     ≤n[ m<n⇒k+m*k≤n*k aN xN<yN ]
          yN *n aN            ≡≤n[ sym (toℕ*homo y a) ]
          toℕ (y * a)
        ≤nEnd

  le' :  fromℕ (toℕ (a + x * a)) ≤ fromℕ (toℕ (y * a))
  le' =  fromℕ-mono-≤ le

------------------------------------------------------
*bs1-mono-< :  ∀ bs → (_* (bs 1#)) Preserves _<_ ⟶ _<_
*bs1-mono-< bs {x} {y} x<y =
                   subst₂ _<_ (fromℕ∘toℕ (x * bs1)) (fromℕ∘toℕ (y * bs1)) le'
  where
  bs1 = bs 1#;   xN = toℕ x;   yN = toℕ y;   bs1N = toℕ bs1

  xN<yN : xN <n yN
  xN<yN = toℕ-mono-< {x} {y} x<y

  pbs1N  = predN bs1N
  0<bs1N = 0<toℕ-bs1 bs

  bs1N≡1+pbs1N :  bs1N ≡ 1+ pbs1N
  bs1N≡1+pbs1N =  sym (NatProp0.suc∘pred 0<bs1N)

  le :  toℕ (x * bs1) <n toℕ (y * bs1)
  le =
     ≤nBegin
       1+ (toℕ (x * bs1))     ≡≤n[ cong 1+_ (toℕ*homo x bs1) ]
       1+ (xN *n bs1N)        ≡≤n[ cong (1+_ ∘ (xN *n_)) bs1N≡1+pbs1N ]
       1+ (xN *n (1+ pbs1N))   ≤n[ NatProp0.*suc-mono-< pbs1N xN<yN ]
       yN *n (1+ pbs1N)       ≡≤n[ cong (yN *n_) (sym bs1N≡1+pbs1N) ]
       yN *n bs1N             ≡≤n[ sym (toℕ*homo y bs1) ]
       toℕ (y * bs1)
     ≤nEnd

  le' :  fromℕ (toℕ (x * bs1)) < fromℕ (toℕ (y * bs1))
  le' =  fromℕ-mono-< le

------------------------------------
*2-mono-< :  _*2 Preserves _<_ ⟶ _<_
*2-mono-< {x} {y} x<y =
                      begin x *2      ≡[ *2≗*2bin x ]
                            x * 2'    <[ *bs1-mono-< [ 0b ] {x} {y} x<y ] 
                            y * 2'    ≡[ sym (*2≗*2bin y) ]
                            y *2
                      ∎