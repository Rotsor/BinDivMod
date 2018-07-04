

-- This is by  Ulf Norell:
-- a suport for reasoning with inequalities.

-- "In response to https://lists.chalmers.se/pipermail/agda/2017/009872.html "

module LtReasoning where

open import Agda.Builtin.Equality

infix 0 case_of_
case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

-- Equality reasoning --

module InequalityReasoning {a b} {A : Set a}
              (_<_ : A → A → Set b)
              (_≤_ : A → A → Set b)
              (leq-refl     : ∀ {x y}   → x ≡ y → x ≤ y)
              (lt-trans     : ∀ {x y z} → x < y → y < z → x < z)
              (leq-trans    : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
              (lt/leq-trans : ∀ {x y z} → x < y → y ≤ z → x < z)
              (leq/lt-trans : ∀ {x y z} → x ≤ y → y < z → x < z)
  where

  data _≲_ (x y : A) : Set b where
    strict    : x < y → x ≲ y
    nonstrict : x ≤ y → x ≲ y

  module _ {x y : A} where
    ⟦_⟧ : x ≲ y → Set b
    ⟦ strict    _ ⟧ = x < y
    ⟦ nonstrict _ ⟧ = x ≤ y

    infix -1 begin_
    begin_ : (p : x ≲ y) → ⟦ p ⟧
    begin strict    p = p
    begin nonstrict p = p

  infixr 0 eqReasoningStep ltReasoningStep leqReasoningStep
  infix  1 _∎

  syntax eqReasoningStep x q p = x ≡[ p ] q
  eqReasoningStep : ∀ (x : A) {y z} → y ≲ z → x ≡ y → x ≲ z
  x ≡[ x=y ] strict    y<z = strict    (case x=y of λ where refl → y<z)
  x ≡[ x=y ] nonstrict y≤z = nonstrict (case x=y of λ where refl → y≤z)
    -- ^ Note: don't match on the proof here, we need to decide strict vs 
    -- nonstrict for neutral proofs

  syntax ltReasoningStep x q p = x <[ p ] q
  ltReasoningStep : ∀ (x : A) {y z} → y ≲ z → x < y → x ≲ z
  x <[ x<y ] strict    y<z = strict (lt-trans x<y y<z)
  x <[ x<y ] nonstrict y≤z = strict (lt/leq-trans x<y y≤z)

  syntax leqReasoningStep x q p = x ≤[ p ] q
  leqReasoningStep : ∀ (x : A) {y z} → y ≲ z → x ≤ y → x ≲ z
  x ≤[ x≤y ] strict    y<z = strict    (leq/lt-trans x≤y y<z)
  x ≤[ x≤y ] nonstrict y≤z = nonstrict (leq-trans x≤y y≤z)

  _∎ : ∀ (x : A) → x ≲ x
  x ∎ = nonstrict (leq-refl refl)


-- Example -----------------------------------

{-
  Bin : Set
  0# 0bs1 0bs'1 bs1 bs'1 2bin : Bin
  _*2 : Bin → Bin
  _+_ _*_ : Bin → Bin → Bin
  _<_ _≤_ : Bin → Bin → Set

  leq-refl : ∀ {x y} → x ≡ y → x ≤ y
  lt-trans : ∀ {x y z} → x < y → y < z → x < z
  leq-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  lt/leq-trans : ∀ {x y z} → x < y → y ≤ z → x < z
  leq/lt-trans : ∀ {x y z} → x ≤ y → y < z → x < z


infix 7 _*2
infixl 7 _*_
infixl 6 _+_
infix 3 _<_ _≤_

open InequalityReasoning _<_ _≤_ leq-refl lt-trans leq-trans lt/leq-trans 
                                                             leq/lt-trans

  step-1 : 0bs1 ≡ bs1 * 2bin
  step-2 : bs1 * 2bin < bs'1 * 2bin
  step-3 : bs'1 * 2bin ≡ bs'1 *2
  step-4 : bs'1 *2 ≡ 0# + 0bs'1

goal : 0bs1 < 0# + 0bs'1
goal =
  begin 0bs1           ≡[ step-1 ]
        bs1 * 2bin     <[ step-2 ]
        bs'1 * 2bin    ≡[ step-3 ]
        bs'1 *2        ≡[ step-4 ]
        0# + 0bs'1
  ∎

goal' : 0bs1 < 0# + 0bs'1
goal' =
  begin 0bs1           ≤[ leq-refl step-1 ]
        bs1 * 2bin     <[ step-2 ]
        bs'1 * 2bin    ≤[ leq-refl step-3 ] 
        bs'1 *2        ≡[ step-4 ]
        0# + 0bs'1
  ∎

test : bs'1 * 2bin ≤ 0# + 0bs'1
test =
  begin bs'1 * 2bin  ≤[ leq-refl step-3 ]
        bs'1 *2      ≡[ step-4 ]
        0# + 0bs'1
  ∎
-}