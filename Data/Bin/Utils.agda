module Data.Bin.Utils where

  open import Data.Digit
  open import Data.Bin hiding (suc)
  open import Data.Fin
  open import Data.List

  _%2 : Bin → Bin
  0# %2 = 0#
  ([] 1#) %2 = [] 1#
  ((zero ∷ _) 1#) %2 = 0#
  ((suc zero ∷ _) 1#) %2 = [] 1#
  ((suc (suc ()) ∷ _) 1#) %2

  bitToBin : Bit → Bin
  bitToBin zero = 0#
  bitToBin (suc zero) = [] 1#
  bitToBin (suc (suc ()))
