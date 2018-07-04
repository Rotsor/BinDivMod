{-                                                            
This file is a part of the library  Binary-3.2.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.  

Binary-3.1  is free software: you can redistribute it and/or modify it 
under the terms of the GNU General Public License.
See  license.txt.
-}

module Bin1 where

open import Level            using () renaming (zero to 0ℓ) 
open import Function         using (id; _∘_; _$_; case_of_; flip) 
open import Algebra          using (Monoid)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Unary   using (Decidable)
open import Relation.Binary 
  using (Rel; Reflexive; Symmetric; Transitive; Asymmetric; Antisymmetric; 
         _⇒_; Irreflexive; Trichotomous; Tri; IsDecEquivalence; _Respects₂_; 
         _Preserves_⟶_; DecSetoid; IsStrictTotalOrder; IsPreorder; 
         IsPartialOrder; StrictTotalOrder; IsTotalOrder; IsDecTotalOrder; 
         DecTotalOrder
        )
  renaming (Decidable to Decidable₂) 
open import Relation.Binary.PropositionalEquality as PE using 
                     (_≡_; _≢_; _≗_; cong; cong₂; subst; subst₂; refl; sym; 
                                     trans; isEquivalence; resp₂; decSetoid)
open PE.≡-Reasoning
open import Relation.Binary.Consequences
import Relation.Binary.StrictToNonStrict as StrictToNonStrict
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤)
open import Data.Sum     using (_⊎_; inj₁; inj₂)           
open import Data.Product using (proj₁; proj₂; _,_; ∃) 
open import Data.Digit   using (Bit; Expansion)
import Data.Fin as Fin
import Data.Fin.Properties as FinProp 
open import Data.List using (List; []; _∷_; _∷ʳ_; [_]; _++_; reverse; 
                                                             replicate)
                      renaming (length to ln)
open import Data.List.Properties as ListProp using 
                      (∷-injective; ∷ʳ-injective; length-++; length-replicate)
import Relation.Binary.List.Pointwise as Pointwise          
import Data.List.Relation.Lex.Strict as StrictLex
open import Data.List.Any using (Any)
open import Data.Nat using (ℕ; zero; z≤n; s≤s; ≤-pred)
     renaming (suc to 1+_; pred to predN; _+_ to _+n_; _∸_ to _∸n_; 
               _*_ to _*n_; _≤_ to _≤n_; _<_ to _<n_; _>_ to _>n_; 
               _≤?_ to _≤?n_; Ordering to Orderingℕ
              )
open import Data.Nat.Properties as NProp using (m≤m+n)
     renaming (+-comm to +n-comm; ≤-antisym to ≤n-antisym; 
               ≤-reflexive to ≤n-reflexive; ≤-refl to ≤n-refl; 
               ≤-trans to ≤n-trans; module ≤-Reasoning to ≤n-Reasoning
              )
open ≤n-Reasoning using () renaming (begin_ to ≤nBegin_; _∎ to _≤nEnd;
                                     _≡⟨_⟩_ to _≡≤n[_]_; _≤⟨_⟩_ to _≤n[_]_)

-- of application ---
open import NatProp0 using (0<1+n; n*2≡n+n)
open import List0    using (++[]; reverse-injective-≡; length-xs:x; 
                                                       replicate-m+n)
open import Bin0 using 
     (_←→_; Bin; toBits; fromBits; fromBits-aux; bitLength; _≡b_; _≢b_; _<_; 
      _>_; _≮_; _≤_; _≰_; _≥_; toℕ; 0b; 1b; ⊥b; _∈_; _∉_; _∈?_; lexBit<; suc; 
      pred; _*2; shift; _+_; _*_; 2^_
     )
     renaming (1bin to 1'; 2bin to 2')



--****************************************************************************
++assoc = Monoid.assoc (ListProp.++-monoid Bit)

open Bin  

-- (Bin, _≡_) is a decidable setoid

≢sym :  ∀ {α} {A : Set α} → Symmetric (_≢_ {A = A})
≢sym =  (_∘ sym) 

bitDecSetoid = FinProp.decSetoid 2
open DecSetoid bitDecSetoid using () renaming (_≟_ to _≟b_)

0b≢1b : 0b ≢b 1b   --
0b≢1b ()

1b≢0b : 1b ≢b 0b   -- 
1b≢0b ()

≢0b⇒≡1b : ∀ b → (b ≢b 0b) → (b ≡b 1b)
≢0b⇒≡1b 1b _     =  refl
≢0b⇒≡1b 0b 0b≢0b =  ⊥-elim (0b≢0b refl)
≢0b⇒≡1b ⊥b 

≢1b⇒≡0b : ∀ b → (b ≢b 1b) → (b ≡b 0b)
≢1b⇒≡0b 0b _     =  refl
≢1b⇒≡0b 1b 1b≢1b =  ⊥-elim (1b≢1b refl)
≢1b⇒≡0b ⊥b

≟0b : Decidable (_≡b 0b)
≟0b = (_≟b 0b)

≟1b : Decidable (_≡b 1b)
≟1b = (_≟b 1b)

0≢bs1 :  ∀ bs → 0# ≢ bs 1#   
0≢bs1 _ () 

bs1≢0 :  ∀ bs → bs 1# ≢ 0#   
bs1≢0 _ () 

≢0#⇒≡bs1 :  ∀ {a} → a ≢ 0# → ∃ (\bs → a ≡ bs 1#)

≢0#⇒≡bs1 {bs 1#} _   =  (bs , refl)
≢0#⇒≡bs1 {0#}    0≢0 =  ⊥-elim (0≢0 refl) 

*2≗2bin* :  _*2 ≗ (2' *_)
*2≗2bin* 0#      =  refl
*2≗2bin* (bs 1#) =  refl 

1#-injective : ∀ {as bs} → as 1# ≡ bs 1# → as ≡ bs
1#-injective refl = refl

toBits-injective :  ∀ {a b} → toBits a ≡ toBits b → a ≡ b  -- new

toBits-injective {0#}    {0#}     _            =  refl
toBits-injective {bs 1#} {bs' 1#} bs++1≡bs'++1 =  cong _1# bs≡bs'
                 where
                 bs≡bs' = proj₁ (∷ʳ-injective bs bs' bs++1≡bs'++1 )

toBits-injective {0#} {bs 1#} [0b]≡bs++1b =  ⊥-elim (0b≢1b 0b≡1b)
                 where
                 0b≡1b = proj₂ (∷ʳ-injective [] bs [0b]≡bs++1b)

toBits-injective {bs 1#} {0#} bs++1b≡[0b] =  ⊥-elim (1b≢0b 1b≡0b)
                 where
                 1b≡0b = proj₂ (∷ʳ-injective bs [] bs++1b≡[0b])

------------------------------------------------------------------------------
infix 4 _≟_ _≟ₑ_

_≟ₑ_ : ∀ {base} → Decidable₂ (_≡_ {A = Expansion base})
_≟ₑ_ []       []       = yes refl
_≟ₑ_ []       (_ ∷ _)  = no λ()
_≟ₑ_ (_ ∷ _) []        = no λ()
_≟ₑ_ (x ∷ xs) (y ∷ ys) with x FinProp.≟ y | xs ≟ₑ ys
... | _        | no xs≢ys = no (xs≢ys ∘ proj₂ ∘ ∷-injective)
... | no  x≢y  | _        = no (x≢y   ∘ proj₁ ∘ ∷-injective)
... | yes refl | yes refl = yes refl

_≟_ : Decidable₂ {A = Bin} _≡_
0#    ≟ 0#    = yes refl
0#    ≟ bs 1# = no λ()
as 1# ≟ 0#    = no λ()
as 1# ≟ bs 1# with as ≟ₑ bs
... | yes refl  = yes refl
... | no  as≢bs = no (as≢bs ∘ 1#-injective)

≡-isDecEquivalence : IsDecEquivalence _≡_
≡-isDecEquivalence = record { isEquivalence = isEquivalence
                            ; _≟_           = _≟_
                            }

≡-decSetoid : DecSetoid _ _
≡-decSetoid = decSetoid _≟_


------------------------------------------------------------------------
-- (Bin _≡_ _<_) is a strict total order

module SLexBit = StrictLex   -- old  StrictLex.Lex {A = Bit} 
open SLexBit using (base; this; next)

open Tri

_bit<_ :  Rel Bit 0ℓ
_bit<_ =  Fin._<_ {2}

bit<-trans : Transitive _bit<_
bit<-trans = FinProp.<-trans {2} 

bit<-asym : Asymmetric _bit<_
bit<-asym bN<b'N b'N<bN =  NProp.<-asym bN<b'N b'N<bN

bit<-irrefl : Irreflexive _≡_ _bit<_
bit<-irrefl refl bN<b'N =  NProp.<-irrefl refl bN<b'N

bit<-resp≡ :  _bit<_ Respects₂ _≡_
bit<-resp≡ =  
           ((\{x} → subst (x bit<_)) , (\{y} → subst (_bit< y)))

trichot-≡-bit< =  FinProp.cmp {2} 

open Pointwise using () renaming ([] to []p; _∷_ to _∷p_)

_=p_ :  Rel (List Bit) 0ℓ
_=p_ =  Pointwise.Rel _≡b_

lexBit> :  Rel (List Bit) 0ℓ
lexBit> =  flip lexBit<

lexBit≮ :  Rel (List Bit) 0ℓ
lexBit≮ x =  ¬_ ∘ lexBit< x

lexBit≯ :  Rel (List Bit) 0ℓ
lexBit≯ x =  ¬_ ∘ lexBit> x

lexBit<-trans : Transitive lexBit<
lexBit<-trans = StrictLex.<-transitive {A = Bit} isEquivalence 
                                                 bit<-resp≡ bit<-trans

lexBit<-asym : Asymmetric lexBit<
lexBit<-asym = StrictLex.<-asymmetric {A = Bit} sym bit<-resp≡ bit<-asym

lexBit<-irrefl : Irreflexive _=p_ lexBit<
lexBit<-irrefl = StrictLex.<-irreflexive {A = Bit} bit<-irrefl 


lexCompare = StrictLex.<-compare {A = Bit} sym trichot-≡-bit<
             -- lexicographic comparison of bit lists

lexBit-≈⇒≮ :  _=p_ ⇒ lexBit≮ 
lexBit-≈⇒≮ {bs} {bs'} bs=p=bs' =
                      case lexCompare bs bs'
                      of \ 
                      { (tri≈ bs≮bs' _      _) → bs≮bs'
                      ; (tri< _      bs≠bs' _) → ⊥-elim (bs≠bs' bs=p=bs')
                      ; (tri> _      bs≠bs' _) → ⊥-elim (bs≠bs' bs=p=bs')
                      }

lexBit-<⇒≯ : lexBit< ⇒ lexBit≯ 
lexBit-<⇒≯ {bs} {bs'} bs<bs' =
                      case lexCompare bs bs'
                      of \ 
                      { (tri< _      _ bs≯bs') → bs≯bs'
                      ; (tri≈ bs≮bs' _ _     ) → ⊥-elim (bs≮bs' bs<bs')
                      ; (tri> bs≮bs' _ _     ) → ⊥-elim (bs≮bs' bs<bs')
                      }


lexBit<-byPrefix : (xs ys : List Bit) → {xs' ys' : List Bit} → ln xs ≡ ln ys →
                            lexBit< xs ys → lexBit< (xs ++ xs') (ys ++ ys')

lexBit<-byPrefix _        _        _           (base ())
lexBit<-byPrefix []       (_ ∷ _)  ()
lexBit<-byPrefix _        _        _           (this x<y)       =  this x<y
lexBit<-byPrefix (_ ∷ xs) (_ ∷ ys) |xxs|≡|yys| (next x≡y xs<ys) = 
                                 next x≡y 
                                      (lexBit<-byPrefix xs ys |xs|≡|ys| xs<ys)
                                 where
                                 |xs|≡|ys| = cong predN |xxs|≡|yys|


lexBit<-bySuffix :  (xs xs' ys ys' : List Bit) → xs =p ys → 
                    lexBit< xs' ys' ←→ lexBit< (xs ++ xs') (ys ++ ys')

lexBit<-bySuffix []       _   (_ ∷ _)  _   ()
lexBit<-bySuffix (_ ∷ _)  _   []       _   ()
lexBit<-bySuffix []       xs' []       ys' _                 =  (id , id)
lexBit<-bySuffix (x ∷ xs) xs' (_ ∷ ys) ys' (refl ∷p xs=p=ys) =  (to , from)
   where
   to :  lexBit< xs' ys' → lexBit< ((x ∷ xs) ++ xs') ((x ∷ ys) ++ ys')
   to xs'<ys' =  next refl xs++xs'<ys+ys' 
      where
      xs++xs'<ys+ys' = proj₁ (lexBit<-bySuffix xs xs' ys ys' xs=p=ys) xs'<ys'

   from :  lexBit< ((x ∷ xs) ++ xs') ((x ∷ ys) ++ ys') → lexBit< xs' ys' 
   from (next _ xs+xs'<ys+ys') = 
                  proj₂ (lexBit<-bySuffix xs xs' ys ys' xs=p=ys) xs+xs'<ys+ys'

   from (this x<x) =  ⊥-elim (bit<-irrefl refl x<x)

------------------------------------------------------------------------------
<-trans : Transitive _<_

<-trans (inj₁ l<l') (inj₁ l'<l'')          =  inj₁ (NProp.<-trans l<l' l'<l'')
<-trans {b} {_} {_} (inj₁ l<l') (inj₂ (l'≡l'' , _)) =  inj₁ l<l''
                                             where
                                             l     = ln (toBits b)
                                             l<l'' = subst (l <n_) l'≡l'' l<l'

<-trans {_} {_} {b''} (inj₂ (l≡l' , _)) (inj₁ l'<l'') =   inj₁ l<l''
                                    where
                                    l''   = ln (toBits b'') 
                                    l<l'' = subst (_<n l'') (sym l≡l') l'<l''

<-trans {_} {_} {b''} (inj₂ (l≡l' , bsR<bs'R)) (inj₂ (l'≡l'' , bs'R<bs''R)) =
                                                      inj₂ (l≡l'' , bsR<bs''R)
                            where
                            l≡l''     = trans l≡l' l'≡l''
                            bsR<bs''R = lexBit<-trans bsR<bs'R  bs'R<bs''R

<-asym : Asymmetric _<_
<-asym {_} {_} (inj₁ l<l')   (inj₁ l'<l)       =  NProp.<-asym l<l' l'<l
<-asym {_} {_} (inj₁ l<l')   (inj₂ (l'≡l , _)) =  NProp.<⇒≢ l<l' (sym l'≡l)
<-asym {_} {_} (inj₂ (l≡l' , _)) (inj₁ l'<l)   =  NProp.<⇒≢ l'<l (sym l≡l')

<-asym {_} {_} (inj₂ (l≡l' , bs<bs')) (inj₂ (l'≡l , bs'<bs)) = 
                                                    lexBit<-asym bs<bs' bs'<bs

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl (inj₁ l<l')                     = NProp.<-irrefl refl l<l'
<-irrefl {b} {b'} b≡b' (inj₂ (l≡l' , bs<bs')) = lexBit<-irrefl bs=p=bs' bs<bs'
                                     where
                                     bs     = reverse (toBits b)
                                     bs'    = reverse (toBits b')
                                     bs≡bs' = cong (reverse ∘ toBits) b≡b'

                                     bs=p=bs' : bs =p bs'
                                     bs=p=bs' = Pointwise.≡⇒Rel≡ bs≡bs'

<⇒≢ :  {a b : Bin} → a < b → a ≢ b
<⇒≢ {a} {b} a<b a≡b = 
                    b≮a b<a  where b≮a = <-asym {a} {b} a<b 
                                   b<a = subst₂ _<_ a≡b (sym a≡b) a<b 

>⇒≢ :  {a b : Bin} → a > b → a ≢ b
>⇒≢ {a} {b} b<a =  ≢sym (<⇒≢ b<a)  

≡⇒≮ :  {a b : Bin} → a ≡ b → a ≮ b
≡⇒≮ {a} {b} a≡b a<b =  
                    <⇒≢ {a} {b} a<b a≡b 

<-resp-≡ :  _<_ Respects₂ _≡_
<-resp-≡ =  
         ((\{x} → subst (x <_)) , (\{y} → subst (_< y)))

<⇒≱ :  {a b : Bin} → a < b → b ≰ a
<⇒≱ {a} {b} a<b (inj₁ b<a) =  <-asym {a} {b} a<b b<a 
<⇒≱         a<b (inj₂ b≡a) =  ≡⇒≮ (sym b≡a) a<b 

≤⇒≯ :  {a b : Bin} → a ≤ b → b ≮ a 
≤⇒≯ a≤b b<a =
            <⇒≱ b<a a≤b

≤,≢⇒< :  ∀ {a b} → a ≤ b → a ≢ b → a < b
≤,≢⇒< (inj₁ a<b) _   =  a<b
≤,≢⇒< (inj₂ a≡b) a≢b =  ⊥-elim (a≢b a≡b)


<-≤-trans :  {a b c : Bin} → a < b → b ≤ c → a < c

<-≤-trans {a} {b} {c} a<b (inj₁ b<c) =  <-trans {a} {b} {c} a<b b<c
<-≤-trans {a} {_} {_} a<b (inj₂ b≡c) =  subst (a <_) b≡c a<b

≤-<-trans :  {a b c : Bin} → a ≤ b → b < c → a < c

≤-<-trans {a} {b} {c} (inj₁ a<b) b<c =  <-trans {a} {b} {c} a<b b<c 
≤-<-trans {_} {_} {c} (inj₂ a≡b) b<c =  subst (_< c) (sym a≡b) b<c


compareN = NProp.<-cmp  

------------------------------------------------------------------------------
<-cmp : Trichotomous _≡_ _<_
<-cmp a b = 
          cmp (compareN l l')
  where
  bs  = toBits a;     bs'  = toBits b
  l   = ln bs;        l'   = ln bs'
  bsR = reverse bs;   bs'R = reverse bs'

  cmp :  Tri (l <n l') (l ≡ l') (l >n l') → Tri (a < b) (a ≡ b) (a > b)

  cmp (tri< l<l' _ _) =  tri< a<b (<⇒≢ {a} {b} a<b) (<-asym {a} {b} a<b)
                         where
                         a<b = inj₁ l<l'

  cmp (tri> _ _ l>l') =  tri> (<-asym {b} {a} a>b) a≢b a>b  
                         where
                         a>b = inj₁ l>l'
                         b≢a = <⇒≢ {b} {a} a>b
                         a≢b = b≢a ∘ sym

  cmp (tri≈ _ l≡l' _) =  
      case lexCompare bsR bs'R 
      of \ 
      { (tri< bsR<bs'R _ _) → let a<b = inj₂ (l≡l' , bsR<bs'R) 
                              in 
                              tri< a<b (<⇒≢ {a} {b} a<b) (<-asym {a} {b} a<b)

      ; (tri> _ _ bsR>bs'R) → let l'≡l = sym l≡l'
                                  a>b  = inj₂ (l'≡l , bsR>bs'R) 
                                  b≢a  = <⇒≢ {b} {a} a>b
                                  a≢b  = b≢a ∘ sym
                              in  
                              tri> (<-asym {b} {a} a>b) a≢b a>b  

      ; (tri≈ _ bsR=p=bs'R _) → 
                let
                  bsR≡bs'R :  bsR ≡ bs'R  
                  bsR≡bs'R =  Pointwise.Rel≡⇒≡ bsR=p=bs'R  

                  bs≡bs' : bs ≡ bs'
                  bs≡bs' = reverse-injective-≡ bsR≡bs'R  

                  a≡b = toBits-injective bs≡bs'  
               in
               tri≈ (≡⇒≮ {a} {b} a≡b) a≡b (≡⇒≮ {b} {a} (sym a≡b))
      }

------------------------------------------------------------------------------
<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = isEquivalence
  ; trans         = \ {a b c} → <-trans {a} {b} {c}
  ; compare       = <-cmp
  }

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder = record
  { Carrier            = Bin
  ; _≈_                = _≡_
  ; _<_                = _<_
  ; isStrictTotalOrder = <-isStrictTotalOrder
  }

------------------------------------------------------------------------------
module ToNonstrict = StrictToNonStrict (_≡_ {A = Bin}) _<_ 

≤-refl :  Reflexive _≤_
≤-refl {x} =  inj₂ refl 

≤-reflexive :  _≡_ ⇒ _≤_
≤-reflexive =  inj₂ 

≤-trans : Transitive _≤_
≤-trans = ToNonstrict.trans isEquivalence <-resp-≡ 
                                          (\ {x y z} → <-trans {x} {y} {z})

_<?_ : Decidable₂ _<_
x <? y  with  <-cmp x y 
... | tri< x<y _ _ =  yes x<y
... | tri≈ x≮y _ _ =  no x≮y
... | tri> x≮y _ _ =  no x≮y

_≤?_ : Decidable₂ _≤_
x ≤? y  with  <-cmp x y 
... | tri< x<y _   _   =  yes (inj₁ x<y)
... | tri≈ _   x≡y _   =  yes (inj₂ x≡y)
... | tri> x≮y x≢y x>y =  no x≰y
                          where x≰y : ¬ x ≤ y
                                x≰y (inj₁ x<y) = x≮y x<y
                                x≰y (inj₂ x≡y) = x≢y x≡y

----------------------------------------
≤-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ   
≤-decTotalOrder = 
               record{ Carrier         = Bin
                     ; _≈_             = _≡_ {A = Bin}
                     ; _≤_             = _≤_ 
                     ; isDecTotalOrder = isDecTotalOrder } 
  where
  isPreorder : IsPreorder _≡_ _≤_
  isPreorder = record{ isEquivalence = isEquivalence 
                     ; reflexive     = ≤-reflexive
                     ; trans         = ≤-trans }

  ≤-antisym : Antisymmetric _≡_ _≤_
  ≤-antisym = ToNonstrict.antisym isEquivalence 
                                   (\ {x y z} → <-trans {x} {y} {z}) <-irrefl

  isPartialOrder : IsPartialOrder _≡_ _≤_
  isPartialOrder = record{ isPreorder = isPreorder; antisym = ≤-antisym }

  total : Relation.Binary.Total _≤_
  total = ToNonstrict.total <-cmp 

  isTotalOrder : IsTotalOrder _≡_ _≤_ 
  isTotalOrder = record{ isPartialOrder = isPartialOrder;  total = total }

  isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
  isDecTotalOrder =
            record{ isTotalOrder = isTotalOrder;  _≟_ = _≟_;  _≤?_ = _≤?_ }


------------------------------------------------------------------------------
0b<1b : 0b bit< 1b
0b<1b = 0<1+n

[0b]<[1b] :  lexBit< (0b ∷ []) (1b ∷ [])
[0b]<[1b] =  this 0b<1b

0<1 :  0# < 1'
0<1 =  inj₂ (refl , [0b]<[1b])

1<bbs1 :  ∀ b bs → 1' < (b ∷ bs) 1#
1<bbs1 b bs = 
         inj₁ 1<|bbs1| 
         where
         1<|bbs1| = 
              ≤nBegin 
                2                     ≤n[ m≤m+n 2 (ln bs) ] 
                1+ (1+ ln bs)        ≡≤n[ cong 1+_ (sym (length-xs:x 1b bs)) ] 
                1+ (ln (bs ∷ʳ 1b))   ≡≤n[ refl ]
                ln (b ∷ (bs ∷ʳ 1b))
              ≤nEnd  

≢0⇒0< :  ∀ {a} → a ≢ 0# → 0# < a

≢0⇒0< {0#}          0≢0 =  ⊥-elim (0≢0 refl)
≢0⇒0< {[] 1#}       _   =  0<1 
≢0⇒0< {(b ∷ bs) 1#} _   =  <-trans {0#} {1'} {(b ∷ bs) 1#} 0<1 (1<bbs1 b bs)

--------------------------
0<bs1 :  ∀ bs → 0# < bs 1#

0<bs1 []       =  inj₂ (refl , [0b]<[1b])
0<bs1 (_ ∷ bs) =  inj₁ 1<1+|bs:1|
      where
      1<1+|bs:1| :  1 <n 1+ (ln (bs ∷ʳ 1b)) 
      1<1+|bs:1| =  
         ≤nBegin 2                    ≤n[ m≤m+n 2 (ln bs) ] 
                 2 +n (ln bs)        ≡≤n[ cong 1+_ (sym (length-xs:x 1b bs)) ] 
                 1+ (ln (bs ∷ʳ 1b)) 
         ≤nEnd

∣_∣ = bitLength

1≤|x| :  (x : Bin) → 1 ≤n ∣ x ∣ 
1≤|x| 0#      =  ≤n-refl
1≤|x| (bs 1#) =  ≤nBegin 1             ≤n[ m≤m+n 1 (ln bs) ]
                         1+ (ln bs)   ≡≤n[ sym (length-xs:x 1b bs) ] 
                         ∣ bs 1# ∣ 
                 ≤nEnd

1≤bs1 :  ∀ bs → 1' ≤ bs 1#
1≤bs1 []       =  ≤-refl
1≤bs1 (b ∷ bs) =  inj₁ lt
      where
      lt = inj₁ $ ≤nBegin 
                    2                 ≤n[ m≤m+n 2 (ln bs) ]
                    2 +n ln bs       ≡≤n[ cong 1+_ (sym (length-xs:x 1b bs)) ]
                    1+ ∣ bs 1# ∣     ≡≤n[ refl ]
                    ∣ (b ∷ bs) 1# ∣
                  ≤nEnd
              
≮0 :  ∀ a → a ≮ 0#
≮0 a a<0 =  case a ≟ 0# of \ { (yes a≡0) → <-irrefl a≡0 a<0 
                             ; (no a≢0)  → let 0<a = ≢0⇒0< a≢0
                                           in  <-asym {0#} {a} 0<a a<0  
                             }

0≤ :  ∀ a → 0# ≤ a
0≤ 0#      =  ≤-refl 
0≤ (bs 1#) =  inj₁ (0<bs1 bs)

≤0⇒≡0 :  ∀ a → a ≤ 0# → a ≡ 0#
≤0⇒≡0 0#      _     =  refl 
≤0⇒≡0 (bs 1#) bs1≤0 =  ⊥-elim (<⇒≱ (0<bs1 bs) bs1≤0)

≰⇒> :  ∀ {a b} → a ≰ b → a > b
≰⇒> {a} {b} a≰b =  case <-cmp a b of \ 
                                { (tri> _   _   a>b) → a>b
                                ; (tri< a<b _   _  ) → ⊥-elim (a≰b (inj₁ a<b))
                                ; (tri≈ _   a≡b _  ) → ⊥-elim (a≰b (inj₂ a≡b))
                                }

≮⇒≥ :  ∀ {a b} → a ≮ b → a ≥ b
≮⇒≥ {a} {b} a≮b =  
                case <-cmp a b of \ 
                                { (tri> _   _   b<a) → inj₁ b<a
                                ; (tri≈ _   a≡b _  ) → inj₂ (sym a≡b)
                                ; (tri< a<b _   _  ) → ⊥-elim (a≮b a<b)
                                }

∣_∣-mono-≤ :  ∣_∣ Preserves _≤_ ⟶ _≤n_
∣_∣-mono-≤ (inj₂ x≡y)                     =  ≤n-reflexive 
                                                (cong (ln ∘ toBits) x≡y)
∣_∣-mono-≤ (inj₁ (inj₁ |bs|<|bs'|))       =  NProp.<⇒≤ |bs|<|bs'|
∣_∣-mono-≤ (inj₁ (inj₂ (|bs|≡|bs'| , _))) =  ≤n-reflexive |bs|≡|bs'|


------------------------------------------------------------------------------
shift≗++ :  ∀ e bs → shift e (bs 1#) ≡ ((replicate e 0b) ++ bs) 1#

shift≗++ 0      _  =  refl
shift≗++ (1+ e) bs =  
  begin 
    shift (1+ e) (bs 1#)                 ≡⟨ refl ⟩
    shift e ((0b ∷ bs) 1#)               ≡⟨ shift≗++ e (0b ∷ bs) ⟩
    ((replicate e 0b) ++ (0b ∷ bs)) 1#   ≡⟨ cong _1# $ sym $ 
                                            ++assoc (replicate e 0b) [ 0b ] bs
                                          ⟩
    (((replicate e 0b) ∷ʳ 0b) ++ bs) 1#  ≡⟨ cong (_1# ∘ (_++ bs))  
                                                (sym (replicate-m+n e 1 0b)) ⟩
    ((replicate (e +n 1) 0b) ++ bs) 1#   
                                    ≡⟨ cong (\z → ((replicate z 0b) ++ bs) 1#)
                                            (+n-comm e 1) ⟩
    ((replicate (1+ e) 0b) ++ bs) 1#     
  ∎

toBits-2^ :  ∀ n → toBits (2^ n) ≡ (replicate n 0b) ∷ʳ 1b
toBits-2^ n = 
  begin
    toBits (2^ n)                          ≡⟨ refl ⟩
    toBits (shift n 1')                    ≡⟨ cong toBits (shift≗++ n []) ⟩
    toBits (((replicate n 0b) ++ []) 1#)   ≡⟨ refl ⟩
    ((replicate n 0b) ++ []) ∷ʳ 1b         ≡⟨ ++assoc (replicate n 0b) [] 
                                                                    [ 1b ]  ⟩
    (replicate n 0b) ∷ʳ 1b
  ∎

record ShiftWhile≤ (bs bs' : List Bit) (bs1≤bs'1 : bs 1# ≤ bs' 1#) :  Set
  where
  constructor shiftWhile≤′ 

  -- This represents   max [ n | 2^n * (bs 1#) ≤ bs' 1# ].

  field  d : ℕ   
   
  zeroes : List Bit 
  zeroes = replicate d 0b 

  field  shifted≤ :  (zeroes ++ bs) 1# ≤ bs' 1#
         next>    :  (0b ∷ (zeroes ++ bs)) 1# > bs' 1#


-------------------------------------------------------------
shiftWhile≤ :  (bs bs' : List Bit) → (leq : bs 1# ≤ bs' 1#) → 
                                                       ShiftWhile≤ bs bs' leq 
shiftWhile≤ bs bs' bs1≤bs'1 =  aux (|bs'| ∸n |bs|) refl
  where
  |bs| = ln bs;   |bs'| = ln bs';   bs:1 = bs ∷ʳ 1b;    bs':1 = bs' ∷ʳ 1b  
  bs1  = bs 1#;   bs'1  = bs' 1#;   |bs:1| = ln bs:1;   |bs':1| = ln bs':1  

  |bs:1|≤|bs':1| :  ln bs:1 ≤n ln bs':1
  |bs:1|≤|bs':1| =  ∣_∣-mono-≤ bs1≤bs'1 

  |bs|≤|bs'| :  |bs| ≤n |bs'|  
  |bs|≤|bs'| =  ≤nBegin 
                  |bs|             ≡≤n[ cong predN (sym (length-xs:x 1b bs)) ] 
                  predN |bs:1|      ≤n[ NProp.pred-mono |bs:1|≤|bs':1| ]
                  predN |bs':1|    ≡≤n[ cong predN (length-xs:x 1b bs') ] 
                  |bs'| 
                ≤nEnd

  aux :  (d : ℕ) → d ≡ |bs'| ∸n |bs| →  ShiftWhile≤ bs bs' bs1≤bs'1 
  aux 0 0≡|bs'|-|bs| = 
                     shiftWhile≤′ 0 bs1≤bs'1 (inj₁ |bs'1|<|0bs1|)
      where
      |bs'|≤|bs|    = NatProp0.∸≡0⇒≤ (sym 0≡|bs'|-|bs|)
      |bs|≡|bs'|    = ≤n-antisym |bs|≤|bs'| |bs'|≤|bs|
      |bs'1|<|0bs1| =  
              ≤n-reflexive
              (begin 
                1+ (ln (bs' ∷ʳ 1b))    ≡⟨ cong 1+_ (length-xs:x 1b bs') ⟩ 
                1+ (1+ |bs'|)          ≡⟨ cong (2 +n_) (sym |bs|≡|bs'|) ⟩ 
                1+ (1+ |bs|)           ≡⟨ cong 1+_ (sym (length-xs:x 1b bs)) ⟩ 
                1+ (ln (bs ∷ʳ 1b))     ≡⟨ refl ⟩
                ln (0b ∷ (bs ∷ʳ 1b))
               ∎ 
              )
              
  aux (1+ d) d'≡|bs'|-|bs| =  aux0 (<-cmp 0zrs:bs1 bs'1) 
    where
    d'       = 1+ d;             zrs     = replicate d 0b;    0zrs = 0b ∷ zrs
    zrs:bs   = zrs ++ bs;        0zrs:bs = 0b ∷ zrs:bs     
    00zrs:bs = 0b ∷ 0b ∷ zrs:bs

    zrs:bs1 = zrs:bs 1#;   0zrs:bs1 = 0zrs:bs 1#

    <zrs:bs>:1   = zrs:bs ∷ʳ 1b;   <0zrs:bs>:1  = 0zrs:bs ∷ʳ 1b  
    <00zrs:bs>:1 = 00zrs:bs ∷ʳ 1b

    |zrs|        = ln zrs;          |zrs:bs|       = ln zrs:bs   
    |0zrs:bs|    = ln 0zrs:bs;      |00zrs:bs|     = ln 00zrs:bs 
    |<zrs:bs>:1| = ln <zrs:bs>:1;   |<00zrs:bs>:1| = ln <00zrs:bs>:1

    |zrs|≡d = length-replicate d

    d'+|bs|≡|bs'| =  
            begin d' +n |bs|                ≡⟨ cong (_+n |bs|) d'≡|bs'|-|bs| ⟩
                  (|bs'| ∸n |bs|) +n |bs|   ≡⟨ +n-comm (|bs'| ∸n |bs|) |bs| ⟩ 
                  |bs| +n (|bs'| ∸n |bs|)   ≡⟨ NProp.m+n∸m≡n |bs|≤|bs'| ⟩
                  |bs'|
            ∎

    |0zrs:bs|≡|bs'| =  
              begin |0zrs:bs|          ≡⟨ length-++ 0zrs ⟩
                    ln 0zrs +n |bs|    ≡⟨ refl ⟩
                    1+ |zrs| +n |bs|   ≡⟨ cong ((_+n |bs|) ∘ 1+_) |zrs|≡d ⟩
                    d' +n |bs|         ≡⟨ d'+|bs|≡|bs'| ⟩ 
                    |bs'|
              ∎    

    |bs':1|<|<00zrs:bs>:1| :  |bs':1| <n |<00zrs:bs>:1|
    |bs':1|<|<00zrs:bs>:1| = 
                  ≤n-reflexive
                  (begin
                     1+ |bs':1|       ≡⟨ cong 1+_ (length-xs:x 1b bs') ⟩ 
                     2 +n |bs'|       ≡⟨ cong (2 +n_) (sym |0zrs:bs|≡|bs'|) ⟩ 
                     2 +n |0zrs:bs|   ≡⟨ refl ⟩ 
                     1+ |00zrs:bs|    ≡⟨ sym (length-xs:x 1b 00zrs:bs) ⟩
                     |<00zrs:bs>:1|
                   ∎
                  )
    
    --------------------------------------------------------------------------
    aux0 :  Tri (0zrs:bs1 < bs'1) (0zrs:bs1 ≡ bs'1) (0zrs:bs1 > bs'1) → 
                                                   ShiftWhile≤ bs bs' bs1≤bs'1
    aux0 (tri< 0zrs:bs1<bs'1 _ _) = 
                                 shiftWhile≤′ d' (inj₁ 0zrs:bs1<bs'1) 
                                                 (inj₁ |bs':1|<|<00zrs:bs>:1|)

    aux0 (tri≈ _ 0zrs:bs1≡bs'1 _) = shiftWhile≤′ d' (inj₂ 0zrs:bs1≡bs'1) 
                                                 (inj₁ |bs':1|<|<00zrs:bs>:1|)

    aux0 (tri> _ _ 0zrs:bs1>bs'1) =  shiftWhile≤′ d (inj₁ zrs:bs1<bs'1) 
                                                    0zrs:bs1>bs'1
         where
         |<zrs:bs>:1|<|bs':1| =  
               ≤n-reflexive
               (begin 1+ |<zrs:bs>:1|  ≡⟨ cong 1+_ (length-xs:x 1b zrs:bs) ⟩
                  1+ (1+ |zrs:bs|)     ≡⟨ refl ⟩
                  1+ |0zrs:bs|         ≡⟨ cong 1+_ |0zrs:bs|≡|bs'| ⟩
                  1+ |bs'|             ≡⟨ sym (length-xs:x 1b bs') ⟩
                  |bs':1| 
                ∎
               )

         zrs:bs1<bs'1 =  inj₁ |<zrs:bs>:1|<|bs':1|

------------------------------------------------------------------------------
cons-0b-ifNonempty :  List Bit → List Bit
cons-0b-ifNonempty []       = []
cons-0b-ifNonempty (b ∷ bs) = 0b ∷ b ∷ bs

cutTrailing-0b :  List Bit → List Bit
cutTrailing-0b []        =  []
cutTrailing-0b (⊥b ∷ _)
cutTrailing-0b (1b ∷ bs) =  1b ∷ (cutTrailing-0b bs)
cutTrailing-0b (0b ∷ bs) =  cons-0b-ifNonempty (cutTrailing-0b bs) 

------------------------------------------------------------------------------
fromBits-0:bs-as*2 :  ∀ bs → fromBits (0b ∷ bs) ≡ (fromBits bs) *2
fromBits-0:bs-as*2 bs =
                      aux <bs> refl
  where
  <bs> = fromBits bs

  aux :  (x : Bin) → x ≡ <bs> →  fromBits (0b ∷ bs) ≡  (fromBits bs) *2
  aux 0# 0≡<bs> =
            begin 
              fromBits (0b ∷ bs)     ≡⟨ refl ⟩
              fromBits-aux 0b <bs>   ≡⟨ cong (fromBits-aux 0b) (sym 0≡<bs>) ⟩
              fromBits-aux 0b 0#     ≡⟨ refl ⟩
              0#                     ≡⟨ refl ⟩
              0# *2                  ≡⟨ cong _*2 0≡<bs> ⟩
              <bs> *2
            ∎

  aux (bs' 1#) bs'1≡<bs> =
      begin
        fromBits (0b ∷ bs)         ≡⟨ refl ⟩
        fromBits-aux 0b <bs>       ≡⟨ cong (fromBits-aux 0b) (sym bs'1≡<bs>) ⟩
        fromBits-aux 0b (bs' 1#)   ≡⟨ refl ⟩
        (0b ∷ bs') 1#              ≡⟨ refl ⟩
        (bs' 1#) *2                ≡⟨ cong _*2 bs'1≡<bs> ⟩
        <bs> *2
      ∎

------------------------------------------------------------------------------
|<fromBits-bs>*2|-≤-1+|fromBits-bs| :  
                          ∀ bs →  ∣ (fromBits bs) *2 ∣  ≤n  1+ ∣ fromBits bs ∣
--
-- (for  fromBits bs ≢ 0#,  this is actually equality)

|<fromBits-bs>*2|-≤-1+|fromBits-bs| bs =  aux <bs> refl
  where
  <bs> = fromBits bs

  aux :  (x : Bin) → x ≡ <bs> →  ∣ (fromBits bs) *2 ∣  ≤n  1+ ∣ fromBits bs ∣  
  aux 0# 0≡<bs> = 
                ≤nBegin ∣ <bs> *2 ∣   ≡≤n[ cong (∣_∣ ∘ _*2) (sym 0≡<bs>) ] 
                        1              ≤n[ m≤m+n 1 ∣ <bs> ∣ ] 
                        1+ ∣ <bs> ∣  
                ≤nEnd

  aux (bs' 1#) bs'1≡<bs> = 
           ≤n-reflexive $
           begin ∣ <bs> *2 ∣         ≡⟨ cong (∣_∣ ∘ _*2) (sym bs'1≡<bs>) ⟩
                 ∣ (0b ∷ bs') 1# ∣   ≡⟨ refl ⟩
                 1+ ∣ bs' 1# ∣       ≡⟨ cong (1+_ ∘ ∣_∣) bs'1≡<bs> ⟩
                 1+ ∣ <bs> ∣  
           ∎ 

------------------------------------------------------------------------------
open Any 

1∉bs⇒fromBits-bs≡0 :  ∀ bs → 1b ∉ bs → fromBits bs ≡ 0#

1∉bs⇒fromBits-bs≡0 []        _     =  refl
1∉bs⇒fromBits-bs≡0 (⊥b ∷ _)
1∉bs⇒fromBits-bs≡0 (0b ∷ bs) 1∉0bs =
     begin
       fromBits (0b ∷ bs)              ≡⟨ refl ⟩
       fromBits-aux 0b (fromBits bs)   ≡⟨ cong (fromBits-aux 0b)
                                               (1∉bs⇒fromBits-bs≡0 bs 1∉bs) ⟩
       fromBits-aux 0b 0#              ≡⟨ refl ⟩
       0#
     ∎
     where 1∉bs = 1∉0bs ∘ there

1∉bs⇒fromBits-bs≡0 (1b ∷ _) 1∉1bs =  ⊥-elim (1∉1bs (here refl))

------------------------------------------------------------------------------
1∈bs⇒|fromBits-bs|≤|bs| :  ∀ bs → 1b ∈ bs → ∣ fromBits bs ∣ ≤n ln bs

1∈bs⇒|fromBits-bs|≤|bs| []        ()
1∈bs⇒|fromBits-bs|≤|bs| (⊥b ∷ _) 
1∈bs⇒|fromBits-bs|≤|bs| (1b ∷ bs) _ =  aux <bs> refl (1b ∈? bs) 
  where          
  <bs> = fromBits bs

  aux :  (x : Bin) → x ≡ <bs> → Dec (1b ∈ bs) → 
                                ∣ (fromBits-aux 1b <bs>) ∣ ≤n 1+ ln bs
  aux 0# 0≡<bs> _ = 
      ≤nBegin 
        ∣ fromBits (1b ∷ bs) ∣     ≡≤n[ refl ]
        ∣ fromBits-aux 1b <bs> ∣   ≡≤n[ cong (∣_∣ ∘ (fromBits-aux 1b)) 
                                                             (sym 0≡<bs>) ]
        ∣ fromBits-aux 1b 0# ∣     ≡≤n[ refl ]
        1                           ≤n[ m≤m+n 1 (ln bs) ]
        1+ ln bs                   ≡≤n[ refl ]
        ln (1b ∷ bs)
      ≤nEnd    

  aux (bs' 1#) bs'1≡<bs> (no 1∉bs) =  ⊥-elim (bs1≢0 bs' bs'1≡0)
                                      where
                                      <bs>≡0 = 1∉bs⇒fromBits-bs≡0 bs 1∉bs
                                      bs'1≡0 = trans bs'1≡<bs> <bs>≡0

  aux (bs' 1#) bs'1≡<bs> (yes 1∈bs) = 
    ≤nBegin 
      ∣ fromBits (1b ∷ bs) ∣        ≡≤n[ refl ]
      ∣ fromBits-aux 1b <bs> ∣      ≡≤n[ cong (∣_∣ ∘ fromBits-aux 1b) 
                                                         (sym bs'1≡<bs>) ]
      ∣ fromBits-aux 1b (bs' 1#) ∣  ≡≤n[ refl ]
      ∣ (1b ∷ bs') 1# ∣             ≡≤n[ refl ]
      1+ ∣ bs' 1# ∣                 ≡≤n[ cong (1+_ ∘ ∣_∣) bs'1≡<bs> ]
      1+ ∣ <bs> ∣                    ≤n[ s≤s (1∈bs⇒|fromBits-bs|≤|bs| bs 1∈bs)
                                       ]
      1+ ln bs                      ≡≤n[ refl ]
      ln (1b ∷ bs)
    ≤nEnd    

1∈bs⇒|fromBits-bs|≤|bs| (0b ∷ _)  (here 1b≡0b) =  ⊥-elim (0b≢1b (sym 1b≡0b))
1∈bs⇒|fromBits-bs|≤|bs| (0b ∷ bs) (there 1∈bs) =  aux <bs> refl
  where
  <bs> = fromBits bs

  aux :  (x : Bin) → x ≡ <bs> →  ∣ (fromBits-aux 0b <bs>) ∣ ≤n 1+ ln bs
  aux 0# 0≡<bs> = 
    ≤nBegin 
      ∣ fromBits-aux 0b <bs> ∣    ≡≤n[ cong  (∣_∣ ∘ (fromBits-aux 0b))
                                                              (sym 0≡<bs>) ]
      ∣ fromBits-aux 0b 0# ∣      ≡≤n[ refl ]  
      1                            ≤n[ m≤m+n 1 (ln bs) ] 
      1+ ln bs
    ≤nEnd

  aux (bs' 1#) bs'1≡<bs> = 
    ≤nBegin 
      ∣ fromBits-aux 0b <bs> ∣      ≡≤n[ cong (∣_∣ ∘ fromBits-aux 0b)
                                                          (sym bs'1≡<bs>) ] 
      ∣ fromBits-aux 0b (bs' 1#) ∣  ≡≤n[ refl ] 
      ∣ (0b ∷ bs') 1# ∣             ≡≤n[ refl ] 
      1+ ∣ (bs' 1#) ∣               ≡≤n[ cong (1+_ ∘ ∣_∣) bs'1≡<bs> ]
      1+ ∣ <bs> ∣                    ≤n[ s≤s (1∈bs⇒|fromBits-bs|≤|bs| bs 1∈bs)
                                       ]
      1+ ln bs
    ≤nEnd


------------------------------------------------------------------------------
|fromBits-bs|≤1+|bs| :  ∀ bs → ∣ fromBits bs ∣ ≤n (1+ ln bs)
|fromBits-bs|≤1+|bs| bs =  
     case 
         1b ∈? bs
     of \ 
     { (yes 1∈bs) → let |fromBits-bs|≤|bs| : ∣ fromBits bs ∣ ≤n ln bs
                        |fromBits-bs|≤|bs| = 1∈bs⇒|fromBits-bs|≤|bs| bs 1∈bs
                      
                        |bs|≤1+|bs| : ln bs ≤n 1+ (ln bs)
                        |bs|≤1+|bs| = NProp.n≤1+n (ln bs)
                    in
                    ≤n-trans |fromBits-bs|≤|bs| |bs|≤1+|bs|

     ; (no 1∉bs) → let fromBits-bs≡0 = 1∉bs⇒fromBits-bs≡0 bs 1∉bs 
                   in
                   ≤nBegin ∣ fromBits bs ∣   ≡≤n[ cong ∣_∣ fromBits-bs≡0 ]
                           1                  ≤n[ m≤m+n 1 (ln bs) ]
                           1+ ln bs
                   ≤nEnd
     }


------------------------------------------------------------------------------
2^suc :  ∀ n → 2^ (1+ n) ≡ (2^ n) *2
2^suc n = 
  begin 
    2^ (1+ n)                            ≡⟨ refl ⟩
    shift (1+ n) 1'                      ≡⟨ shift≗++ (1+ n) [] ⟩
    ((replicate (1+ n) 0b) ++ []) 1#     ≡⟨ refl ⟩
    (0b ∷ ((replicate n 0b) ++ [])) 1#   ≡⟨ cong (_1# ∘ (0b ∷_)) 
                                                 (++[] (replicate n 0b)) ⟩
    (0b ∷ (replicate n 0b)) 1#           ≡⟨ refl ⟩
    ((replicate n 0b) 1#) *2             ≡⟨ cong (_*2 ∘ _1#)
                                                 (sym (++[] (replicate n 0b)))
                                          ⟩
    (((replicate n 0b) ++ []) 1#) *2     ≡⟨ cong _*2 (sym (shift≗++ n [])) ⟩
    (2^ n) *2
  ∎

--------------------------------------
|2^n|≡1+n :  (n : ℕ) → ∣ 2^ n ∣ ≡ 1+ n
|2^n|≡1+n n = 
  begin 
    ∣ 2^ n ∣                             ≡⟨ refl ⟩
    ∣ shift n ([] 1#) ∣                  ≡⟨ cong ∣_∣ (shift≗++ n []) ⟩
    ln (((replicate n 0b) ++ []) ∷ʳ 1b)  ≡⟨ length-xs:x 1b 
                                                   ((replicate n 0b) ++ []) ⟩
    1+ ln ((replicate n 0b) ++ [])       ≡⟨ cong (1+_ ∘ ln) 
                                                 (++[] (replicate n 0b)) ⟩
    1+ ln (replicate n 0b)               ≡⟨ cong 1+_ (length-replicate n) ⟩
    1+ n
  ∎

----------------------------------------------------------
|bs1|<|2^|bs1|| :  ∀ bs →  ∣ bs 1# ∣ <n ∣ (2^ ∣ bs 1# ∣) ∣ 
|bs1|<|2^|bs1|| bs =
                   ≤n-reflexive (sym (|2^n|≡1+n ∣ bs 1# ∣))

------------------------------------------------------------------------------
|fromBits-bbs|<2+|bs| :  ∀ b bs →  ∣ fromBits (b ∷ bs) ∣  <n  2 +n (ln bs)

|fromBits-bbs|<2+|bs| b bs  with 1b ∈? (b ∷ bs)

... | yes 1∈bbs =   s≤s (1∈bs⇒|fromBits-bs|≤|bs| (b ∷ bs) 1∈bbs)
... | no  1∉bbs  =
            ≤nBegin
              1+ ∣ fromBits bbs ∣   ≡≤n[ cong (1+_ ∘ ∣_∣)
                                              (1∉bs⇒fromBits-bs≡0 bbs 1∉bbs) ]
              1+ ∣ 0# ∣             ≡≤n[ refl ]
              2                      ≤n[ m≤m+n 2 (ln bs) ]
              2 +n (ln bs)          
            ≤nEnd
            where bbs = b ∷ bs


fromBits-bbs<2^|bbs| :  ∀ b bs → fromBits (b ∷ bs) < 2^ (ln (b ∷ bs))
fromBits-bbs<2^|bbs| b bs = 
                inj₁ $ 
                ≤nBegin 1+ ∣ fromBits bbs ∣   ≤n[ |fromBits-bbs|<2+|bs| b bs ]
                        2 +n (ln bs)         ≡≤n[ sym (|2^n|≡1+n (ln bbs))  ]
                        ∣ 2^ (ln bbs) ∣ 
                ≤nEnd
                where bbs = b ∷ bs