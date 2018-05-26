{-# OPTIONS  --no-termination-check #-}

module Data.Bin.BinDivNt where

  open import Data.Bin
  open import Data.Bin.Properties
  open import Data.Product
  open import Relation.Binary
  open StrictTotalOrder <-strictTotalOrder
  
  open import Relation.Nullary
  open import Data.Bin.Utils
  open import Data.Bin.Minus

  _divMod-nt_ : Bin → Bin → (Bin × Bin)
  a divMod-nt b with a <? b
  ... | yes _ = (fromℕ 0 , a)
  ... | no _ with a divMod-nt (b *2)
  ... | (d , m) with m <? b
  ... | yes _ = (d *2 , m)
  ... | no _ = (fromℕ 1 + (d *2) , m - b)
