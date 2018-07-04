{-# OPTIONS  --no-termination-check #-}
module Data.Bin.DivModTests where

open import Data.Bin.DivMod
open Everything using (BinFin; _divMod_; result)
open import IO
open import Data.Bin hiding (suc; fromℕ)
open import Data.String hiding (_≟_)
open import Data.Unit hiding (_≟_)
open import Coinduction
open import Data.List
open import Data.Char hiding (_≟_)
open import Data.Digit hiding (toDigits)
open import Data.Fin hiding (_+_; fromℕ; _≟_)
open import Data.Bin.Bijection using (fromℕ)

showBits : Bin → String
showBits x = fromList (Data.List.reverse (Data.List.map showDigit (toBits x)))

open import Relation.Nullary.Decidable
import Data.Bin.Properties
-- eq =  Data.Bin.Properties._≟_
open import Relation.Binary
open import Data.Bin.Properties using (<-strictTotalOrder)
open StrictTotalOrder <-strictTotalOrder using (_≟_)

toDigits : (base : Bin) → {≢0 : False (base ≟ (fromℕ 0))} → Bin → List (BinFin base)
toDigits _ 0# = []
toDigits base {≢0} x with (x divMod base) {≢0}
... | result q r _ = r ∷ toDigits base {≢0} q -- still need to prove termination of this

showBinDigit : Bin → Char
showBinDigit 0# = '0'
showBinDigit ([] 1#) = '1'
showBinDigit ((zero ∷ []) 1#) = '2'
showBinDigit ((suc zero ∷ []) 1#) = '3'
showBinDigit ((zero ∷ zero ∷ []) 1#) = '4'
showBinDigit ((suc zero ∷ zero ∷ []) 1#) = '5'
showBinDigit ((zero ∷ suc zero ∷ []) 1#) = '6'
showBinDigit ((suc zero ∷ suc zero ∷ []) 1#) = '7'
showBinDigit ((zero ∷ zero ∷ zero ∷ []) 1#) = '8'
showBinDigit ((suc zero ∷ zero ∷ zero ∷ []) 1#) = '9'
showBinDigit _ = 'x'

open import Function
open import Data.Product

showDigits : Bin → String
showDigits x = fromList (Data.List.reverse (Data.List.map (showBinDigit ∘ proj₁) (toDigits (fromℕ 10) x)))

test : Bin → String
test x = showDigits x

go : Bin → IO ⊤
go n = ♯ putStrLn (test n) >> ♯ go (n + (fromℕ 1))

main = run (go (fromℕ 100 * fromℕ 100))
