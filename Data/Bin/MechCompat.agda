module Data.Bin.MechCompat where

open import Data.Bin
open import Data.String using(String; fromList)
import Data.Digit
import Data.List
open import Data.Nat using(ℕ; suc)

1bin = fromℕ 1
2bin = fromℕ 2

infixl 8 _^_

_^_ : Bin → ℕ → Bin
_ ^ 0      =  1bin
x ^ (suc n) =  x * (x ^ n)

showBits : Bin → String
showBits x = fromList (Data.List.reverse (Data.List.map Data.Digit.showDigit (toBits x)))

show = showBits
