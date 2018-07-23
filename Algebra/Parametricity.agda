{- module Algebra.Parametricity where

import Algebra.Syntax as Syntax
open Syntax

open import Level using (Level)

record Related {a b : Level} (A B : Set a) (R : A → B → Set b) : Set ((Level._⊔_ a b)) where
 constructor related
 field
   ₁ : A
   ₂ : B
   r : R ₁ ₂

{- Builtin-env : Set₁
Builtin-env = Related Set Set (λ A B → A → B → Set) -}

Type-Interpretation : Set → Typ → Set
Type-Interpretation V S = V
Type-Interpretation V (Arrow F X) =
  Type-Interpretation V F → Type-Interpretation V X 

Related-values : Builtin-env → Typ → Set
Related-values env S = Related (Related.₁ env) (Related.₂ env) (Related.r env)
Related-values env (Arrow A R) =
  Related-values env A → Related-values env R

{-data Env (B : Builtin-env) : Context → Set where
  □ : Env B □
  _▸_ : ∀ {t X} → (env : Env B t) → Related-values B X → Env B (t ▸ X) -}

{- _▸-env_ : ∀ {V} → ∀ {t X} → (env : Env V t) → Type-Interpretation V X → Env V (t ▸ X)
_▸-env_ = _▸_ -}

-}
