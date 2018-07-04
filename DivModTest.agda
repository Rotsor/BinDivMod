module DivModTest where

open import Foreign.Haskell
open import IO.Primitive
open import Data.String using (String; toCostring)

open import Function  using (_$_; _∘_) 
open import Relation.Binary.PropositionalEquality using (_≢_; sym)
open import Data.List using (List; []; _∷_) 
open import Data.Nat  using (ℕ) renaming (suc to 1+_) 
import Data.Nat.Show as NatShow 
open import Data.Nat.DivMod using () 
                        renaming (DivMod to DivModN; _divMod_ to _divModN_)
import Data.Fin as Fin 

-- of application ---
open import List0  using (concatStr) 
open import Data.Bin.MechCompat using (1bin; 2bin; _^_) 
                  renaming (show to showB)
open import Data.Bin using (Bin; 0b; 1b; 0#; _+_; _*2; _*_; suc; toℕ)
open import Data.Bin.Minus renaming (_-_ to _∸_; pred' to pred)
open import Data.Bin.Properties using (<-strictTotalOrder)

open import Relation.Binary 
  using (Rel; Reflexive; Symmetric; Transitive; Asymmetric; Antisymmetric; 
         _⇒_; Irreflexive; Trichotomous; Tri; IsDecEquivalence; _Respects₂_; 
         _Preserves_⟶_; DecSetoid; IsStrictTotalOrder; IsPreorder; 
         IsPartialOrder; StrictTotalOrder; IsTotalOrder; IsDecTotalOrder; 
         DecTotalOrder
        )
  renaming (Decidable to Decidable₂) 

≢sym :  ∀ {α} {A : Set α} → Symmetric (_≢_ {A = A})
≢sym =  (_∘ sym) 


------------------------------------------------------------------------------
testN : ℕ → (dr : ℕ) → List String 
testN dd dr = 
            let (DivModN.result q rF _) =  dd divModN (1+ dr) 
                r = Fin.toℕ rF
            in
            "dd = " ∷ NatShow.show dd  ∷ "   dr = " ∷ NatShow.show (1+ dr) ∷ 
            "\nq = " ∷ NatShow.show q  ∷ "   r = " ∷ NatShow.show r  ∷ [] 

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

import Data.Bin.Addition
import Data.Bin
import Data.Bin.Bijection

0≢1+x : ∀ x → ¬ (Data.Bin.0# ≡ Data.Bin.suc x)
0≢1+x x eq with trans (cong toℕ eq) (Data.Bin.Addition.+-is-addition (Data.Bin.fromℕ 1) x)
0≢1+x _ _ | ()

import Data.Bin.DivMod

testB :  Bin → (dr : Bin) → List String 
testB dd dr = 
            let 1+dr≢0                  = ≢sym (0≢1+x dr)
                (Data.Bin.DivMod.Everything.DivMod.result q r _) =
                  Data.Bin.DivMod.Everything.divMod dd (suc dr) 1+dr≢0
            in
            "dd = "  ∷ showB dd  ∷  "   dr = " ∷  showB dr  ∷ 
            "\nq = " ∷ showB q   ∷  "   r = "  ∷  showB (Data.Bin.DivMod.Everything.toBin r)   ∷  [] 


open import BinFromString

main = (readFiniteFile "data.txt") >>= putStrLn ∘ toCostring ∘ g
       where
       g : String -> String
       g str = concatStr $ testB dd c
               where       -- test ddN drN
               a : Bin
               a = fromString str

               b = fromString "10101"
               c = fromString "10101010"

               dd = a 
               dr = a 

               ddN = toℕ dd;   drN = toℕ dr
