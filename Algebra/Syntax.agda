
module Algebra.Syntax where
  data Explicitness : Set where
    explicit implicit : Explicitness

  mutual

    data Context : Set

    data Context where
      □ : Context
      _▸_ : ∀ (t : Context) (x : Typ) → Context
    data Typ : Set
    data Prop : (t : Context) → Set

    data Typ where -- type language
      S : Typ
      Arrow : Typ → Typ → Typ

    data Prop where
      Equiv : ∀ {t} → (x y : Term t S) → Prop t
      Forall : ∀ {t} → Explicitness → (T : Typ) → (Prop (t ▸ T)) → Prop t

    data Term : (t : Context) → Typ → Set where -- type language
      Var : ∀ {t T} → Position t T → Term t T
      Apply : ∀ {t} {Q R : Typ} → Term t (Arrow Q R) → Term t Q → Term t R

    _▸'_ : ∀ (t : Context) (x : Typ) → Context
    _▸'_ = _▸_
    
    weaken-term : ∀ {t X T} → Term t T → Term (t ▸' X) T

    data Position : (t : Context) → (T : Typ) → Set where
      here : ∀ t X → Position (t ▸ X) X
      there : ∀ t x y → Position t x → Position (t ▸ y) x

    there' : ∀ t x y → Position t x → Position (t ▸' y) x
    there' = there
    weaken-term (Var x) = Var (there _ _ _ x)
    weaken-term (Apply f x) = Apply (weaken-term f) (weaken-term x)
