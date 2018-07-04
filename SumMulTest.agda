module SumMulTest where

open import Foreign.Haskell
open import IO.Primitive
open import Data.String using (String; toCostring)

open import Function using (_$_; _∘_; case_of_) 
open import Relation.Binary using (Tri; StrictTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≢_; sym)
open import Relation.Nullary using (yes; no)
open import Data.List        using (List; []; _∷_) 
open import Data.Nat         using (ℕ) renaming (suc to 1+_) 
open import Data.Nat.Show    using () renaming (show to showN) 

-- of application ---
open import List0 using (concatStr)
import Data.Bin.Properties
open import Data.Bin.MechCompat using (1bin; 2bin; _^_) 
                  renaming (show to showB)
open import Data.Bin using (Bin; 0b; 1b; 0#; _+_; _*2; _*_; suc; toℕ)
open import Data.Bin.Minus renaming (_-_ to _∸_; pred' to pred)
open import Data.Bin.Properties using (<-strictTotalOrder)
open StrictTotalOrder <-strictTotalOrder using () renaming (compare to <-cmp)


------------------------------------------------------------------------------
-- 3bin a b : Bin
-- 3bin = 1bin + 2bin

_≟_ = Data.Bin.Properties._≟_
{-# TERMINATING #-}
sumUp : Bin → Bin   -- 0 + 1 + .. + a
sumUp a =  aux 0#
        where
        aux : Bin → Bin 
        aux x =  case _≟_ x a  of \ { (yes _) → x
                                          ; (no _)  → x + (aux (suc x))
                                          }
{-# TERMINATING #-}
minusUp : Bin → Bin → Bin
minusUp a b =  aux 0# b       -- (.. ((b ∸ 0) ∸ 1) .. ∸ a)
     where
     aux : Bin → Bin → Bin 
     aux x r =  case _≟_ x a  of \ { (yes _) → r ∸ x
                                         ; (no _)  → aux (suc x) (r ∸ x)
                                         }

open Tri

{-# TERMINATING #-}
sumProducts : Bin → Bin 
sumProducts a =  aux 1bin a    -- sum [i * (a - i) | i <- [1 .. a-1]]
   where
   aux : Bin → Bin → Bin
   aux x y = case <-cmp x y 
             of \ 
             { (tri< _ _ _) → (x * y) + (aux (suc x) (pred y))
             ; (tri≈ _ _ _) → (x * y) 
             ; (tri> _ _ _) → 0#
             } 

testSum∸  :  Bin → List String    -- for  _+_, _∸_  on Bin
testSum∸ a = 
  "a  = "    ∷ showB a ∷  
  "\ns  = "  ∷ showB s ∷  
  "\ns' = "  ∷ showB s' ∷  
  []   
  where
  s  = sumUp a  
  s' = minusUp a s


testSum*  :  Bin → List String    -- for  _+_, _*_  on Bin
testSum* a = 
    "a  = "   ∷ showB a ∷  
    "\ns = "  ∷ showB s ∷  
    []   
    where
    s = sumProducts a  


open import BinFromString

main = (readFiniteFile "data.txt") >>= putStrLn ∘ toCostring ∘ g
       where
       g : String -> String
       g str = concatStr $ 
               -- testSum∸ (Bin0.fromString str)
               testSum* (fromString str)


