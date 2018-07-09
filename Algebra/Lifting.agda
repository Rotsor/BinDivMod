import Algebra
import Algebra.Structures
import Function.Equality
import Function.Equivalence hiding (_∘_)
import Function.Bijection hiding (_∘_)
import Level
import Relation.Binary
import Algebra.FunctionProperties
import Relation.Binary.EqReasoning

open Level renaming (zero to ₀; suc to level-suc)
open Relation.Binary using (Setoid; module Setoid)
open Function.Bijection using (Bijection)

module Algebra.Lifting
  (S₁ S₂ : Setoid ₀ ₀)
  (f : Bijection S₁ S₂) where

  open Algebra.FunctionProperties using (Op₂; LeftIdentity)
  open Algebra.Structures

  open Setoid S₁ using () renaming (Carrier to A₁; _≈_ to _≈₁_; sym to sym₁; refl to refl₁; trans to trans₁)
  open Setoid S₂ using (sym; trans) renaming (Carrier to A₂; _≈_ to _≈₂_; isEquivalence to isEquivalence₂)
  open Bijection f
  open Function.Equality using (_⟨$⟩_; cong; _⟶_; _⇨_)
  open Relation.Binary.EqReasoning S₁ renaming (begin_ to begin₁_; _∎ to _∎₁; _≈⟨_⟩_ to _≈₁⟨_⟩_)
  open Relation.Binary.EqReasoning S₂ renaming (begin_ to begin₂_; _∎ to _∎₂; _≈⟨_⟩_ to _≈₂⟨_⟩_)

  open import Function using (_⟨_⟩_; case_of_)

  from-inj : ∀ {x y} → from ⟨$⟩ x ≈₁ from ⟨$⟩ y → x ≈₂ y
  from-inj {x} {y} eq = (sym (right-inverse-of x)) ⟨ trans ⟩ cong to eq ⟨ trans ⟩ (right-inverse-of y)


  open import Data.Nat
  open import Data.Fin
  level-₁ = level-suc ₀

  data Explicitness : Set where
    explicit implicit : Explicitness

  mutual

    data Context : Set ₀

    data Context where
      □ : Context
      _▸_ : ∀ (t : Context) (x : Typ) → Context
    data Typ : Set ₀
    data Prop : (t : Context) → Set ₀

    data Typ where -- type language
      S : Typ
      Arrow : Typ → Typ → Typ

    data Prop where
      Equiv : ∀ {t} → (x y : Term t S) → Prop t
      Forall : ∀ {t} → Explicitness → (T : Typ) → (Prop (t ▸ T)) → Prop t

    data Term : (t : Context) → Typ → Set ₀ where -- type language
      Var : ∀ {t T} → Position t T → Term t T
      Apply : ∀ {t} {Q R : Typ} → Term t (Arrow Q R) → Term t Q → Term t R

    _▸'_ : ∀ (t : Context) (x : Typ) → Context
    _▸'_ = _▸_
    
    weaken-term : ∀ {t X T} → Term t T → Term (t ▸' X) T

    data Position : (t : Context) → (T : Typ) → Set ₀ where
      here : ∀ t X → Position (t ▸ X) X
      there : ∀ t x y → Position t x → Position (t ▸ y) x

    there' : ∀ t x y → Position t x → Position (t ▸' y) x
    there' = there
    weaken-term (Var x) = Var (there _ _ _ x)
    weaken-term (Apply f x) = Apply (weaken-term f) (weaken-term x)

  open import Data.Product
  open import Function using ()
  _↔_ : ∀ (A B : Set ₀) → Set ₀
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

  open import Data.Unit

  import Function.Inverse as Inverse
  open Inverse using (Inverse)


  Related : ∀ {S₁ S₂ : Setoid ₀ ₀} (B : Inverse S₁ S₂) → Setoid.Carrier S₁ → Setoid.Carrier S₂ → Set
  Related {S₁} B x y =
    let _≈_ = Setoid._≈_ S₁ in
    x ≈ (Inverse.from B ⟨$⟩ y)

  f-inv = Inverse.fromBijection f
  S-rel : A₁ → A₂ → Set
  S-rel = Related f-inv

  abstract

    lift-eq :
      ∀ {x₁ y₁ x₂ y₂}
      → x₁ ≈₁ y₁
      → S-rel x₁ x₂
      → S-rel y₁ y₂
      → x₂ ≈₂ y₂
    lift-eq
      eq
      rel-x
      rel-y
      =
      from-inj (trans₁ (trans₁ (sym₁ rel-x) eq) rel-y)

  Val-rel :
    ∀ (T : Typ)
    → Type-Interpretation S₁ T → Type-Interpretation S₂ T → Set
  Val-rel S v₁ v₂ = S-rel v₁ v₂
  Val-rel (Arrow A R) f₁ f₂ =
    ∀ x₁ x₂ → Val-rel A x₁ x₂ → Val-rel R (f₁ ⟨$⟩ x₁) (f₂ ⟨$⟩ x₂)

  open import Data.Sum

  Val-rel-computer : ∀ (T : Typ) → Set
  Val-rel-computer T =
    let T₁ = Type-Interpretation S₁ T in
    let T₂ = Type-Interpretation S₂ T in
    T₁ ⊎ T₂ → ∃₂ (Val-rel T)

  Env-rel : ∀ {ctx} → Env S₁ ctx → Env S₂ ctx → Set
  Env-rel □ □ = ⊤
  Env-rel {_ ▸ T} (xs ▸ x) (ys ▸ y) = Env-rel xs ys × Val-rel T x y

  record Env* (ctx : Context) : Set where
   constructor related-env
   field
    ₁ : Env S₁ ctx
    ₂ : Env S₂ ctx
    rel : Env-rel ₁ ₂


  Type-Lifter-Type :
    ∀ (T : Typ) → Set
  Type-Lifter-Type T =
   Σ
    (Inverse
     (Setoid-Interpretation S₁ T)
     (Setoid-Interpretation S₂ T))
     (λ f → (
       ∀ a b → Related f a b → Val-rel T a b
     ) ×
     (
       ∀ a b → Val-rel T a b → Related f a b
     ))

  Lifter-type :
    ∀ {ctx} (P : Prop ctx) → Set
  Lifter-type {ctx} P =
      ∀ (E : Env* ctx) →
        Prop-Interpretation (Env*.₁ E) P
      →
        Prop-Interpretation (Env*.₂ E) P

  Var-rel : ∀ {ctx} T (E : Env* ctx) → ∀ x →
    Val-rel T
     (lookup-env {S₁} {ctx} {T} (Env*.₁ E) x)
     (lookup-env {S₂} {ctx} {T} (Env*.₂ E) x)
  Var-rel T (related-env (_ ▸ x₁) (_ ▸ x₂) (_ , rel)) (here t .T) = rel 
  Var-rel T (related-env (₁ ▸ _) (₂ ▸ _) (rel , _)) (there t .T y x) =
    Var-rel T (related-env ₁ ₂ rel) x

  Term-Interpretation-rel :
    ∀ {ctx T} (E : Env* ctx) → (t : Term ctx T)
    → Val-rel T
      (Term-Interpretation (Env*.₁ E) t)
      (Term-Interpretation (Env*.₂ E) t)
  Term-Interpretation-rel {ctx} {T} E (Var x) = Var-rel T E x
  Term-Interpretation-rel {ctx} {T} E (Apply f x) =
    let f-rel = Term-Interpretation-rel E f in
    let x-rel = Term-Interpretation-rel E x in
    f-rel _ _ x-rel

  Comp :
   ∀ {A B C : Setoid ₀ ₀} →
   Setoid.Carrier ((B ⇨ C) ⇨ (A ⇨ B) ⇨ (A ⇨ C))
  Comp =
    record {
      _⟨$⟩_ = λ f →
        record {
         _⟨$⟩_ = Function.Equality._∘_ f ;
         cong = λ g₁=g₂ a₁=a₂ →
            Function.Equality.cong f (g₁=g₂ a₁=a₂)  }
    ; cong = λ f₁=f₂ g₁=g₂ a₁=a₂ → f₁=f₂ (g₁=g₂ a₁=a₂) }

  flipped-Comp :
   ∀ {A B C : Setoid ₀ ₀} →
   Setoid.Carrier ((A ⇨ B) ⇨ ((B ⇨ C) ⇨ (A ⇨ C)))
  flipped-Comp =
    record {
      _⟨$⟩_ = λ g →
        record {
         _⟨$⟩_ = λ f → Function.Equality._∘_ f g ;
         cong = λ f₁=f₂ a₁=a₂ → 
            f₁=f₂ (Function.Equality.cong g a₁=a₂)  }
    ; cong =  λ g₁=g₂ f₁=f₂ a₁=a₂ → f₁=f₂ (g₁=g₂ a₁=a₂) }

  bijection-postcomposition-is-bijection :
   ∀ {A B C : Setoid ₀ ₀} →
   (Inverse B C) → (Inverse (A ⇨ B) (A ⇨ C))
  bijection-postcomposition-is-bijection {A} {B} {C}
    (record { to = b-to-c; from = c-to-b;
     inverse-of = record {
       left-inverse-of = left-inverse-of;
       right-inverse-of = right-inverse-of
     } }) =
   record {
     to = Comp ⟨$⟩ b-to-c ;
     from = Comp ⟨$⟩ c-to-b ;
     inverse-of = record {
       left-inverse-of =
         λ a-to-b a1=a2 →
             Setoid.trans B (left-inverse-of _)
             (Function.Equality.cong a-to-b a1=a2) ;
       right-inverse-of =
         λ a-to-c a1=a2 →
             Setoid.trans C (right-inverse-of _)
             (Function.Equality.cong a-to-c a1=a2)
       } }

  bijection-precomposition-is-bijection :
   ∀ {A B C : Setoid ₀ ₀} →
   (Inverse A B) → (Inverse (A ⇨ C) (B ⇨ C))
  bijection-precomposition-is-bijection {A} {B} {C}
    (record { to = a-to-b; from = b-to-a;
     inverse-of = record {
       left-inverse-of = left-inverse-of;
       right-inverse-of = right-inverse-of
     } }) =
   record {
     to = flipped-Comp ⟨$⟩ b-to-a ;
     from = flipped-Comp ⟨$⟩ a-to-b ;
     inverse-of = record {
       left-inverse-of =
         λ a-to-c a1=a2 →
            Function.Equality.cong a-to-c  (
              Setoid.trans A (left-inverse-of _)
              a1=a2);
       right-inverse-of =
         λ a-to-b a1=a2 →
            Function.Equality.cong a-to-b  (
              Setoid.trans B (right-inverse-of _)
              a1=a2)
       } }
       
    {- record {
      _⟨$⟩_ = λ f →
        record {
         _⟨$⟩_ = Function.Equality._∘_ f ;
         cong = λ g₁=g₂ a₁=a₂ →
            Function.Equality.cong f (g₁=g₂ a₁=a₂)  }
    ; cong = λ f₁=f₂ g₁=g₂ a₁=a₂ → f₁=f₂ (g₁=g₂ a₁=a₂) } -}

{-  flip :
   ∀ {A B C : Setoid ₀ ₀} →
   (A ⇨ (B ⇨ C)) ⟶ (B ⇨ (A ⇨ C))
  flip =
    record {
      _⟨$⟩_ = λ f →
        record { _⟨$⟩_ = λ b →
          record { _⟨$⟩_ = {!!} ; cong = {!!} } ;
        cong = {!!} } ;
      cong = {!!} } -}

{-  Val-rel-computer-impl : ∀ T → Val-rel-computer T
  Val-rel-computer-impl S (inj₁ x) =
    x , (to ⟨$⟩ x) , Setoid.sym S₁ (Inverse.left-inverse-of f-inv x)
  Val-rel-computer-impl S (inj₂ y) =
    from ⟨$⟩ y , y , Setoid.refl S₁
  Val-rel-computer-impl (Arrow A R) f-or-g = {!!} where
    f-big : ∃₂ (Val-rel A) → ∃₂ (Val-rel R)
    f-big (a₁ , a₂ , a-rel) =
       case f-or-g of λ {
         (inj₁ f) → Val-rel-computer-impl R (inj₁ (f ⟨$⟩ a₁)) ;
         (inj₂ g) → Val-rel-computer-impl R (inj₂ (g ⟨$⟩ a₂)) } -}

  Type-Lifter : ∀ T → Type-Lifter-Type T
  Type-Lifter S = f-inv , (λ a b x → x) , λ a b x → x
  Type-Lifter (Arrow A R) =
    let a-inverse , (a-inv-to-rel , a-rel-to-inv) = Type-Lifter A in
    let r-inverse , (r-inv-to-rel , r-rel-to-inv) = Type-Lifter R in
    Inverse._∘_
      (bijection-precomposition-is-bijection a-inverse)    
      (bijection-postcomposition-is-bijection r-inverse)
    , ((λ f₁ f₂ f₁≈lifted-f₂ a₁ a₂ a₁-rel-a₂ →
      r-inv-to-rel _ _
        (Setoid.trans (Setoid-Interpretation S₁ R)
          (f₁≈lifted-f₂ {a₁} (a-rel-to-inv _ _ a₁-rel-a₂ ))
          (cong (Inverse.from r-inverse) (cong f₂ (Inverse.right-inverse-of a-inverse _))) ))
    , λ f₁ f₂ a-rel→r-rel {al} {ar} al=₁ar →
      let ar₂ = Inverse.to a-inverse ⟨$⟩ ar in
       let
        zzz =
         a-inv-to-rel al ar₂
         (
          Setoid.trans (Setoid-Interpretation S₁ A) al=₁ar
           (Setoid.sym (Setoid-Interpretation S₁ A) (Inverse.left-inverse-of a-inverse _)))
       in
       r-rel-to-inv _ _ (a-rel→r-rel _ _ zzz))

  Lifter : ∀ {ctx} (P : Prop ctx) → Lifter-type P
  Lifter (Equiv x y) = λ { E eq₁ → 
    let x-rel = Term-Interpretation-rel E x in
    let y-rel = Term-Interpretation-rel E y in
    lift-eq eq₁ x-rel y-rel }
  Lifter (Forall explicit T P) =
    λ E forall₁ → λ t₂ →
      let t-bijection , (t-related , _blargh) = Type-Lifter T in
      let t₁ = Inverse.from t-bijection ⟨$⟩ t₂ in
      Lifter P
        (related-env
          (Env*.₁ E ▸ t₁)
          (Env*.₂ E ▸ t₂)
          (Env*.rel E , t-related t₁ t₂ (Setoid.refl (Setoid-Interpretation S₁ T))))
        (forall₁ t₁)
  Lifter (Forall implicit T P) =
    λ E forall₁ → λ { t₂ } →
      let t-bijection , (t-related , _blargh) = Type-Lifter T in
      let t₁ = Inverse.from t-bijection ⟨$⟩ t₂ in
      Lifter P
        (related-env
          (Env*.₁ E ▸ t₁)
          (Env*.₂ E ▸ t₂)
          (Env*.rel E , t-related t₁ t₂ (Setoid.refl (Setoid-Interpretation S₁ T))))
        (forall₁ { t₁ })


  s : Typ
  s = S

  Bin-op : Typ
  Bin-op = Arrow S (Arrow S S)

  Comm : Prop (□ ▸ Arrow S (Arrow S S))
  Comm =
      (Forall explicit S
        (Forall explicit S
          (Equiv
            (Apply (
              Apply
                (Var (there _ _ _ (there _ _ _ (here _ _))))
                (Var (there _ _ _ (here _ _))))
                (Var (here _ _)))
            (Apply (
              Apply
                (Var (there _ _ _ (there _ _ _ (here _ _))))
                (Var (here _ _)))
                (Var (there _ _ _ (here _ _))))
            )))

  Lift-Comm = Lifter Comm

{-  record Binary-op : Set _ where
   field
    op1 : Setoid.Carrier (S₁ ⇨ S₁ ⇨ S₁)
    op2 : Setoid.Carrier (S₂ ⇨ S₂ ⇨ S₂)
    correspond : ∀ {x y s t} → from (op1 ⟨$⟩ x ⟨$⟩ y) -}

  module WithOp₂
   (_+₁_ : Op₂ A₁)
   (_+₂_ : Op₂ A₂)
   (+-same : ∀ x y → from ⟨$⟩ (x +₂ y) ≈₁ (from ⟨$⟩ x) +₁ (from ⟨$⟩ y)) where

   module WithCong
     (cong1 : ∀ a b c d → a ≈₁ b → c ≈₁ d → (a +₁ c) ≈₁ (b +₁ d))
     (cong2 : ∀ a b c d → a ≈₂ b → c ≈₂ d → (a +₂ c) ≈₂ (b +₂ d)) where
     Env-plus : Env* (□ ▸ Arrow S (Arrow S S))
     Env-plus =
       related-env
         (□ ▸ record { _⟨$⟩_ = λ x → record { _⟨$⟩_ = λ y →  x +₁ y ; cong = λ eq → cong1 x x _ _ (Setoid.refl S₁) eq } ; cong = λ eq₁ eq₂ → cong1 _ _ _ _ eq₁ eq₂ })
         (□ ▸ record { _⟨$⟩_ = λ x → record { _⟨$⟩_ = λ y →  x +₂ y ; cong = λ eq → cong2 x x _ _ (Setoid.refl S₂) eq } ; cong = λ eq₁ eq₂ → cong2 _ _ _ _ eq₁ eq₂ })
         (tt ,
         (λ a₁ a₂ a-rel b₁ b₂ b-rel →
          Setoid.trans S₁ (cong1 _ _ _ _ a-rel b-rel) (Setoid.sym S₁ (+-same a₂ b₂))))

     lift-comm : (∀ x y → (x +₁ y) ≈₁ (y +₁ x)) → (∀ x y → (x +₂ y) ≈₂ (y +₂ x)) 
     lift-comm = Lift-Comm Env-plus



   lift-comm : (∀ x y → (x +₁ y) ≈₁ (y +₁ x)) → (∀ x y → (x +₂ y) ≈₂ (y +₂ x)) 
   lift-comm comm₁ x y = from-inj (
       begin₁
          from ⟨$⟩ x +₂ y
           ≈₁⟨ +-same x y ⟩
          (from ⟨$⟩ x) +₁ (from ⟨$⟩ y)
           ≈₁⟨ comm₁ (from ⟨$⟩ x) (from ⟨$⟩ y) ⟩
          (from ⟨$⟩ y) +₁ (from ⟨$⟩ x)
           ≈₁⟨ sym₁ (+-same y x) ⟩
          from ⟨$⟩ y +₂ x
       ∎₁
      )

   using-+-same : ∀ {a b c d}
                  → (from ⟨$⟩ a) +₁ (from ⟨$⟩ b) ≈₁ (from ⟨$⟩ c) +₁ (from ⟨$⟩ d)
                  → from ⟨$⟩ a +₂ b ≈₁ from ⟨$⟩ c +₂ d
   using-+-same {a} {b} {c} {d} eq =
    begin₁
     from ⟨$⟩ a +₂ b
      ≈₁⟨ +-same a b ⟩
     (from ⟨$⟩ a) +₁ (from ⟨$⟩ b)
      ≈₁⟨ eq ⟩
     (from ⟨$⟩ c) +₁ (from ⟨$⟩ d)
      ≈₁⟨ sym₁ (+-same c d) ⟩
     from ⟨$⟩ c +₂ d
    ∎₁

   lift-comm' : (∀ x y → (x +₁ y) ≈₁ (y +₁ x)) → (∀ x y → (x +₂ y) ≈₂ (y +₂ x)) 
   lift-comm' comm₁ x y = from-inj (using-+-same (comm₁ (from ⟨$⟩ x) (from ⟨$⟩ y)))

   lift-assoc : (∀ x y z → (x +₁ y) +₁ z ≈₁ x +₁ (y +₁ z)) 
              → (∀ {a b c d} → a ≈₁ b → c ≈₁ d → a +₁ c ≈₁ b +₁ d)
              → (∀ x y z → (x +₂ y) +₂ z ≈₂ x +₂ (y +₂ z))
   lift-assoc assoc₁ +₁-cong x y z = from-inj (using-+-same (
    begin₁
      (from ⟨$⟩ x +₂ y) +₁ fz
       ≈₁⟨ +₁-cong (+-same x y) refl₁ ⟩
      (fx +₁ fy) +₁ fz
       ≈₁⟨ assoc₁ fx fy fz ⟩
      fx +₁ (fy +₁ fz)
       ≈₁⟨ +₁-cong  refl₁ (sym₁ (+-same y z)) ⟩
      fx +₁ (from ⟨$⟩ y +₂ z)
    ∎₁)) where
     fx = from ⟨$⟩ x
     fy = from ⟨$⟩ y
     fz = from ⟨$⟩ z

   +Cong₁ = (∀ {a b c d} → a ≈₁ b → c ≈₁ d → a +₁ c ≈₁ b +₁ d)
   +Cong₂ = (∀ {a b c d} → a ≈₂ b → c ≈₂ d → a +₂ c ≈₂ b +₂ d)

   lift-cong : +Cong₁ → +Cong₂
   lift-cong cong₁ a≈₂b c≈₂d = from-inj (using-+-same (cong₁ (cong from  a≈₂b) (cong from  c≈₂d)))

   lift-isSemigroup : IsSemigroup _≈₁_ _+₁_ → IsSemigroup _≈₂_ _+₂_ 
   lift-isSemigroup isSemigroup = record 
     { isEquivalence = isEquivalence₂
     ; assoc = lift-assoc assoc ∙-cong
     ; ∙-cong = lift-cong ∙-cong
     } where
    open IsSemigroup isSemigroup

   lift-LeftIdentity : ∀ ε → +Cong₁ → LeftIdentity _≈₁_ ε _+₁_ → LeftIdentity _≈₂_ (to ⟨$⟩ ε) _+₂_
   lift-LeftIdentity ε +-cong₁ identityˡ x = from-inj (
    begin₁
     from ⟨$⟩ (to ⟨$⟩ ε) +₂ x
      ≈₁⟨ +-same (to ⟨$⟩ ε) x ⟩
     (from ⟨$⟩ (to ⟨$⟩ ε)) +₁ (from ⟨$⟩ x)
      ≈₁⟨ +-cong₁ (left-inverse-of ε) refl₁ ⟩
     ε +₁ (from ⟨$⟩ x)
      ≈₁⟨ identityˡ (from ⟨$⟩ x) ⟩
     from ⟨$⟩ x
    ∎₁)

   lift-isCommutativeMonoid : ∀ ε → IsCommutativeMonoid _≈₁_ _+₁_ ε → IsCommutativeMonoid _≈₂_ _+₂_ (to ⟨$⟩ ε)
   lift-isCommutativeMonoid ε isCommMonoid = record 
     { isSemigroup = lift-isSemigroup isSemigroup
     ; identityˡ = lift-LeftIdentity ε ∙-cong identityˡ
     ; comm = lift-comm comm
     } where
    open IsCommutativeMonoid isCommMonoid

{-   lift-isCommutativeMonoid : ∀ 0# 1# → IsCommutativeSemiring _≈₁_ _+₁_ _*₁_ 0# 1# → IsCommutativeMonoid _≈₂_ _+₂_ (to ⟨$⟩ ε)
   lift-isCommutativeMonoid ε isCommMonoid = record 
     { isSemigroup = lift-isSemigroup isSemigroup
     ; identityˡ = lift-LeftIdentity ε ∙-cong identityˡ
     ; comm = lift-comm comm
     } where
    open IsCommutativeMonoid isCommMonoid -}
