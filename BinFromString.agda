module BinFromString where

open import Data.List using(List; _∷_; [])
open import Data.Bin using(Bin; 0b; 1b)
open import Data.String using(String)
open import Function using(_∘_)

open import Data.Digit      using (fromDigits; toDigits; Bit)
open import Data.Char using(Char)
charsToBits : List Char → List Bit    -- it also fiters out non-digits
charsToBits []         =  [] 
charsToBits ('0' ∷ cs) =  0b ∷ (charsToBits cs) 
charsToBits ('1' ∷ cs) =  1b ∷ (charsToBits cs) 
charsToBits (_   ∷ cs) =  charsToBits cs

fromString : String → Bin 
fromString =
            Data.Bin.fromBits ∘ Data.List.reverse ∘ charsToBits ∘ Data.String.toList 
