module GCDTest where

open import Foreign.Haskell
open import IO.Primitive
open import Data.String using (String; toCostring)

open import Function using (_$_; _∘_; case_of_) 
open import Relation.Binary.PropositionalEquality using (_≢_; sym)
open import Relation.Nullary using (yes; no)
open import Data.List        using (List; []; _∷_) 
open import Data.Nat         using (ℕ) renaming (suc to 1+_) 
open import Data.Nat.Show    using () renaming (show to showN) 
open import Data.Nat.DivMod  using () 
                        renaming (DivMod to DivModN; _divMod_ to _divModN_)

-- of application ---
open import List0 using (concatStr) 
open import Bin0  using (Bin; 0b; 1b; 0#; 1bin; 2bin; _+_; _*2; _*_; suc; toℕ;
                                                                     _^_)
                  renaming (show to showB)
import Bin1
open import GCD using (GCD; gcd!) 


------------------------------------------------------------------------------
3bin a b : Bin
3bin = 1bin + 2bin
a    = 2bin ^ 20
b    = 3bin ^ 21

{-# TERMINATING #-}
sumGCD : Bin → Bin   -- sum [gcd! x b | x <- [a .. a']]
sumGCD a' =  aux a
             where
             aux : Bin → Bin 
             aux x =  case  Bin1._≟_ x a'  of \ 
                                       { (yes _) → gcd! x b
                                       ; (no _)  → (gcd! x b) + (aux (suc x))
                                       }

testBin :  Bin → List String    -- for  gcd  on Bin
testBin c = 
  "a  = "   ∷ showB a  ∷   "    b = "  ∷  showB b  ∷ 
  "\nc  = " ∷ showB c ∷  
  "\na' = " ∷ showB a' ∷  
  "\ngSum = " ∷ showB gSum  ∷  

  -- "\naN = " ∷ showN aN  ∷   "  bN = " ∷  showN bN ∷   -- expensive
  -- "\ncN = " ∷ showN cN  ∷ 
  []   
  where
  aN = toℕ a;   bN = toℕ b;   cN = toℕ c;   a' = a + c

  gSum = sumGCD (a + c)  -- sum [gcd! x b | x <- [a .. (a+c)]]



main = (readFiniteFile "data.txt") >>= putStrLn ∘ toCostring ∘ g
       where
       g : String -> String
       g str = concatStr $ testBin (Bin0.fromString str)

{-
Example:   putting   1001  to  data.txt  means that  c = 9,

and  testBin  to find and print out the value 

              sum [gcd! x b | x <- [a .. (a + 9)]]
              where
              a = 2bin ^ 20
              b = 3bin ^ 21

Appending  0  to the string in data.txt increses  c  twice.
And one can see the computation cost dependence on the bit length
of  x  in the loop, and on the number  1+c  of the calls for  gcd.  
-}
 
