{-                                                            
This file is a part of the library  Binary-3.2.
Copyright © 2018  Program Systems Institute of Russian Academy of Sciences.  

Binary-3.0  is free software: you can redistribute it and/or modify it 
under the terms of the GNU General Public License.
See  license.txt.
-}

{-# OPTIONS --termination-depth=2 #-}
module Bin0 where

open import Level    using (_⊔_) renaming (zero to 0ℓ)
open import Function using (id; const; flip; _∘_)
open import Algebra.FunctionProperties as FuncProp using (Op₂) 
open import Relation.Nullary           using (¬_)
open import Relation.Nullary.Decidable using ()
open import Relation.Binary using (Rel; DecSetoid) 
                            renaming (Decidable to Decidable₂) 
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Data.Empty   using (⊥-elim)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (uncurry; _,_; _×_; ∃)
open import Data.List as List using (List; []; _∷_; [_]; _++_; reverse) 
                              renaming (length to ln)
open import Data.List.Properties using (length-++)
open import Data.List.Any        using (any)
import Data.List.Membership.Setoid as Membership
open import Relation.Binary.List.StrictLex using (Lex-<) 
open import Data.Char          using (Char)
open import Data.String as Str using (String)
import Data.Fin.Properties as FinP
open import Data.Nat as Nat using (ℕ; zero; z≤n; s≤s)
                            renaming (suc to 1+_;  _∸_ to _∸n_; _<_ to _<n_; 
                                      _≤_ to _≤n_; _≤?_ to _≤?n_; _>_ to _>n_ 
                                     )
open import Data.Digit      using (fromDigits; toDigits; Bit)
open import Data.Fin as Fin using (Fin; zero) renaming (suc to 1+_)
open import Data.Fin.Properties as FP using (_+′_)
open import Data.Bool                 using (Bool; true; false)

import NatProp0  -- of application


------------------------------------------------------------------------------
infix 3 _←→_

_←→_ : ∀ {α β} (A : Set α) → (B : Set β) → Set (α ⊔ β)
_←→_ A B =  (A → B) × (B → A)


-- Bits

pattern 0b = zero
pattern 1b = 1+ zero
pattern ⊥b = 1+ 1+ ()

const-0b const-1b :  Bit → Bit
const-0b = const {A = Bit} 0b

const-1b = const {A = Bit} 1b

infixl 2 _≡b_ _≢b_

_≡b_ =  _≡_ {A = Bit}
_≢b_ =  _≢_ {A = Bit}

bitDecSetoid = FinP.decSetoid 2
bitSetoid    = DecSetoid.setoid bitDecSetoid 

_≟b_ :  Decidable₂ _≡b_
_≟b_ =  DecSetoid._≟_ bitDecSetoid

_∈_ :  Bit → List Bit → Set
_∈_ =  Membership._∈_ bitSetoid 

_∉_ :  Bit → List Bit → Set
_∉_ b =  ¬_ ∘ (b ∈_)

_∈?_ :  Decidable₂ _∈_
_∈?_ b =  any (b ≟b_)


------------------------------------------------------------------------------
-- A comment from Standard: 
-- A representation of binary natural numbers in which there is
-- exactly one representative for every number. The function toℕ below
-- defines the meaning of Bin.

-- `bs 1#` stands for the binary number "1<reverse bs>" e.g.
-- `(0b ∷ [])           1#` represents "10"
-- `(0b ∷ 1b ∷ 1b ∷ []) 1#` represents "1110"

Bin⁺ : Set
Bin⁺ = List Bit

infix 8 _1#

data Bin : Set where
  0#  : Bin
  _1# : (bs : Bin⁺) → Bin

------------------------------------------------------------------------------
1bin =  [] 1#
2bin =  [ 0b ] 1#


shift : ℕ → Bin → Bin          -- optimization for (2^n *_) 
shift 0      x       =  x
shift (1+ _) 0#      =  0#
shift (1+ n) (bs 1#) =  shift n ((0b ∷ bs) 1#)

infixr 8 2^_   -- Power of two.

2^_ : ℕ → Bin
2^ n =  shift n 1bin


-- Converting to a list of bits starting with the _least_ significant one.

toBits : Bin → List Bit
toBits 0#      = [ 0b ]
toBits (bs 1#) = bs ++ [ 1b ]


fromBits-aux : Bit → Bin → Bin

fromBits-aux b  (bs' 1#) = (b ∷ bs') 1#
fromBits-aux 0b 0#       =  0#
fromBits-aux 1b 0#       =  1bin
fromBits-aux ⊥b _

fromBits : List Bit → Bin    -- another implementation for standard
fromBits []       = 0#
fromBits (b ∷ bs) = fromBits-aux b (fromBits bs)

toℕ : Bin → ℕ
toℕ = fromDigits ∘ toBits

bitLength : Bin → ℕ
bitLength = ln ∘ toBits

------------------------------------------------------------------------------
-- Order relation.

infix 4 _<_ _>_ _≤_

lexBit< : Rel Bin⁺ 0ℓ
lexBit< = Lex-< {A = Bit} _≡_ Fin._<_

_<_ : Rel Bin 0ℓ
--                                                     
-- b < b'  when  deg b < deg b'  or                            
--               (deg b ≡ deg b'  and                                     
--                      reverse (toBits b)  is lexicoraphically smaller than  
--                      reverse (toBits b')                 
--               )                                         
b < b' =  let bs  = toBits b;     bs'  = toBits b'
              deg = ln bs;        deg' = ln bs'
              bsR = reverse bs;   bs'R = reverse bs'
          in
          deg <n deg' ⊎ (deg ≡ deg' × lexBit< bsR bs'R)

------------------------------------------------------------------------------
_>_ : Rel Bin 0ℓ
_>_ = flip _<_

_≮_ : Rel Bin 0ℓ
_≮_ x =  ¬_ ∘ (x <_)

_≤_ :  Rel Bin 0ℓ
a ≤ b =  a < b ⊎ a ≡ b

_≥_ :  Rel Bin 0ℓ
_≥_ =  flip _≤_

_≰_ :  Rel Bin 0ℓ
_≰_ x =  ¬_ ∘ (x ≤_)

------------------------------------------------------------------------------
-- Arithmetic

⌊log₂_⌋ : Bin⁺ → ℕ                -- Base 2 logarithm (rounded downwards).
⌊log₂ (b ∷ bs) ⌋ = 1+ ⌊log₂ bs ⌋
⌊log₂ []       ⌋ = 0


infix 7 _*2 _*2+1                 -- Multiplication by 2.

_*2 : Bin → Bin
0#      *2 = 0#
(bs 1#) *2 = (0b ∷ bs) 1#

_*2+1 : Bin → Bin
0#      *2+1 = [] 1#
(bs 1#) *2+1 = (1b ∷ bs) 1#

-- Division by 2, rounded downwards.

⌊_/2⌋ : Bin → Bin
⌊ 0#          /2⌋ = 0#
⌊ [] 1#       /2⌋ = 0#
⌊ (b ∷ bs) 1# /2⌋ = bs 1#

-- Addition.

Carry : Set
Carry = Bit

addBits : Carry → Bit → Bit → Carry × Bit
addBits c b₁ b₂ 
             with c +′ (b₁ +′ b₂)
... | zero           = (0b , 0b)
... | 1+ zero        = (0b , 1b)
... | 1+ 1+ zero     = (1b , 0b)
... | 1+ 1+ 1+ zero  = (1b , 1b)
... | 1+ 1+ 1+ 1+ ()


addCarry : Carry → List Bit → List Bit
addCarry 0b bs        = bs
addCarry 1b []        = 1b ∷ []
addCarry 1b (0b ∷ bs) = 1b ∷ bs
addCarry 1b (1b ∷ bs) = 0b ∷ addCarry 1b bs
addCarry ⊥b _
addCarry _  (⊥b ∷ _) 

mutual 
  addBitLists : Carry → Bin⁺ → Bin⁺ → Bin⁺ 
  addBitLists c []         bs₂        = addCarry c bs₂
  addBitLists c bs₁        []         = addCarry c bs₁
  addBitLists c (b₁ ∷ bs₁) (b₂ ∷ bs₂) = addBL-aux bs₁ bs₂ (addBits c b₁ b₂)

  addBL-aux : Bin⁺ → Bin⁺ → Bit × Bit → Bin⁺
  addBL-aux bs₁ bs₂ (c' , b') =  b' ∷ (addBitLists c' bs₁ bs₂)

addBL : Carry → Bin⁺ → Bin⁺ → Bin⁺ 
addBL = addBitLists
 

infixl 6 _+_

_+_ : Bin → Bin → Bin
a + b = fromBits (addBL 0b (toBits a) (toBits b))

-- Multiplication.

infixl 7 _*_

*aux : Bit → Bin → Bin → Bin 
*aux _  _ 0#       =  0# 
*aux 0b _ (bs' 1#) =  (0b ∷ bs') 1#
*aux 1b y (bs' 1#) =  y + ((0b ∷ bs') 1#)
*aux ⊥b 

_*_ : Bin → Bin → Bin
0#            * _ =  0#
[] 1#         * y =  y
((b ∷ bs) 1#) * y =  *aux b y ((bs 1#) * y)
                              -- (b + 2*(bs 1#)) * y =  b*n + 2*(bs 1# * y)

infixl 8 _^_

_^_ : Bin → ℕ → Bin
_ ^ 0      =  1bin
x ^ (1+ n) =  x * (x ^ n)

suc : Bin → Bin     -- Successor.
suc n = [] 1# + n

-- Division by 2, rounded upwards.

⌈_/2⌉ : Bin → Bin
⌈ n /2⌉ = ⌊ suc n /2⌋


minusCarry-aux :  List Bit → List Bit
minusCarry-aux []            =  1b ∷ []
minusCarry-aux (0b ∷ [])     =  1b ∷ []
minusCarry-aux (0b ∷ b ∷ bs) =  1b ∷ 0b ∷ b ∷ bs
minusCarry-aux (1b ∷ bs)     =  1b ∷ 1b ∷ bs
minusCarry-aux (⊥b ∷ _) 
--
-- this is for subracting 1 from a binary representation
--
minusCarry :  Carry → List Bit → List Bit
minusCarry ⊥b _
minusCarry 0b bs            =  bs
minusCarry 1b []            =  []
minusCarry 1b (⊥b ∷ _)
minusCarry 1b (1b ∷ bs)     =  0b ∷ bs
minusCarry 1b (0b ∷ [])     =  0b ∷ [] 
minusCarry 1b (0b ∷ b ∷ bs) =  minusCarry-aux (minusCarry 1b (b ∷ bs))

predList : List Bit → List Bit 
predList = minusCarry 1b

pred : Bin → Bin
pred = fromBits ∘ predList ∘ toBits

infixl 6 _-'_ 

_-'_ : Op₂ Bit    
x  -' 0b = x
0b -' 1b = 1b
1b -' 1b = 0b
⊥b -' _
_  -' ⊥b

inv : Bit → Bit
inv = (_-' 1b)

charsToBits : List Char → List Bit    -- it also fiters out non-digits
charsToBits []         =  [] 
charsToBits ('0' ∷ cs) =  0b ∷ (charsToBits cs) 
charsToBits ('1' ∷ cs) =  1b ∷ (charsToBits cs) 
charsToBits (_   ∷ cs) =  charsToBits cs

fromString : String → Bin 
fromString =
            fromBits ∘ reverse ∘ charsToBits ∘ Str.toList 

private 
  example0 :  toℕ (fromString "110") ≡ 6   -- example
  example0 =  refl


show : Bin → String
show = Str.fromList ∘ showBitList ∘ reverse ∘ toBits 
       where
       showBitList : List Bit → List Char
       showBitList []        = []
       showBitList (0b ∷ bs) = '0' ∷ (showBitList bs)
       showBitList (1b ∷ bs) = '1' ∷ (showBitList bs)
       showBitList (⊥b ∷ _) 

infix 4 _∣_ 

_∣_ :  Rel Bin 0ℓ
a ∣ b =  ∃ (\q → a * q ≡ b)
