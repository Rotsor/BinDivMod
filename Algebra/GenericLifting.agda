module Algebra.GenericLifting where
  open import Algebra.Syntax
  open import Level using (Level) renaming (zero to ₀)
  open import Relation.Binary using (Setoid; module Setoid)
  import Function.Equality
  open Function.Equality using (_⟨$⟩_; cong; _⟶_; _⇨_)

  open import Data.Product
  open import Function using ()
  _↔_ : ∀ (A B : Set) → Set ₀
  A ↔ B = (A → B) × (B → A)

  Setoid-Interpretation : Setoid ₀ ₀ → Typ → Setoid ₀ ₀
  Setoid-Interpretation V S = V
  Setoid-Interpretation V (Arrow F X) =
    Setoid-Interpretation V F ⇨ Setoid-Interpretation V X 

  Type-Interpretation : Setoid ₀ ₀ → Typ → Set ₀
  Type-Interpretation V x = Setoid.Carrier (Setoid-Interpretation V x)

  data Env (V : Setoid ₀ ₀) : Context → Set ₀ where
    □ : Env V □
    _▸_ : ∀ {t X} → (env : Env V t) → Type-Interpretation V X → Env V (t ▸ X)

  _▸-env_ : ∀ {V} → ∀ {t X} → (env : Env V t) → Type-Interpretation V X → Env V (t ▸ X)
  _▸-env_ = _▸_

  lookup-env : {V : Setoid ₀ ₀} → ∀ {t T} → (env : Env V t) → Position t T → Type-Interpretation V T
  lookup-env (env ▸ x) (here _ _) = x 
  lookup-env (env ▸ x) (there t _ _ pos) =
     (lookup-env env pos) 

  Term-Interpretation : ∀ {V t T} → (env : Env V t) → Term t T → Type-Interpretation V T
  Term-Interpretation env (Var x) = lookup-env env x
  Term-Interpretation env (Apply f x) = Term-Interpretation env f ⟨$⟩ (Term-Interpretation env x)

  Prop-Interpretation : ∀ {V} → ∀ {t} → (env : Env V t) → Prop t → Set ₀
  Prop-Interpretation {V} env (Equiv x y) = Setoid._≈_ V (Term-Interpretation env x) (Term-Interpretation env y)
  Prop-Interpretation {V} env (Forall explicit T P) =
    ∀ (x : Type-Interpretation V T) → Prop-Interpretation (env ▸ x) P
  Prop-Interpretation {V} env (Forall implicit T P) =
    ∀ {x : Type-Interpretation V T} → Prop-Interpretation (env ▸ x) P


  record Related-raw {a b : Level} (A B : Set a) (R : A → B → Set b) : Set (Level._⊔_ a b) where
   constructor related
   field
     ₁ : A
     ₂ : B
     r : R ₁ ₂

  open Related-raw

  Related : ∀ {a b} → Related-raw (Set a) (Set a) (λ A B → A → B → Set b) → Set (Level._⊔_ a b)
  Related (related A B R) = Related-raw A B R

  l₁ = (Level.suc ₀)

  [U] : Related-raw (Set l₁) (Set l₁) (λ A B → A → B → Set (Level.suc ₀))
  [U] = related Set Set (λ A B → A → B → Set)

  open import Data.Nat
  open import Relation.Binary.PropositionalEquality

  [ℕ] : Related [U]
  [ℕ] = related ℕ ℕ _≡_

  import Function.Inverse
  open import Data.Unit

  [=Setoid=] : Related-raw (Set l₁) (Set l₁) (λ A B → A → B → Set)
  [=Setoid=] = related (Setoid ₀ ₀) (Setoid ₀ ₀) Function.Inverse.Inverse

  Val-Rel :
    ∀ (S : Related [=Setoid=]) (T : Typ)
    → Type-Interpretation (₁ S) T → Type-Interpretation (₂ S) T → Set
  Val-Rel s S v₁ v₂ = (r s) v₁ v₂
  Val-Rel S (Arrow A R) f₁ f₂ =
    ∀ x₁ x₂ → Val-Rel A x₁ x₂ → Val-Rel R (f₁ ⟨$⟩ x₁) (f₂ ⟨$⟩ x₂)

  Env-Rel : ∀ {ctx} → (S : Related [=Setoid=]) → Env (₁ S) ctx → Env (₂ S) ctx → Set
  Env-Rel S □ □ = ⊤
  Env-Rel {_ ▸ T} S (xs ▸ x) (ys ▸ y) = Env-Rel S xs ys × Val-Rel S T x y
