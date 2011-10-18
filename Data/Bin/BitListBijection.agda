module Data.Bin.BitListBijection where

  open import Data.List
  open import Data.List.Properties
  import Data.Digit
  open Data.Digit using (Bit)
  open import Data.Fin using (zero; suc; Fin; inject₁) renaming (toℕ to finToℕ)
  open import Data.Nat using (ℕ; zero;suc)

  infix 3 _≈_ _≈ʳ_

  0×_ : ℕ → List Bit
  0× n = replicate n zero

  data _≈_ : List Bit → List Bit → Set where
    equiv : ∀ n m l → l ++ replicate n zero ≈ l ++ replicate m zero

  data _≈ʳ_ : List Bit → List Bit → Set where
    equiv : ∀ n m l → 0× n ++ l ≈ʳ 0× m ++ l

  open import Relation.Binary using (IsEquivalence; Setoid; Reflexive; Symmetric; Transitive)
  import Relation.Binary.PropositionalEquality
  module PropEq = Relation.Binary.PropositionalEquality
  open import Algebra
  import Level

  open import Algebra.FunctionProperties
  open import Data.Product renaming (map to pmap)
  
  ₀ = Level.zero

  open PropEq using (_≡_)

  
  replicate-side-irrelevant : ∀ {A : Set} n (x : A) → replicate n x ++ [ x ] ≡ x ∷ replicate n x
  replicate-side-irrelevant zero x = PropEq.refl
  replicate-side-irrelevant (suc n) x with replicate-side-irrelevant n x
  ... | rec = PropEq.cong (λ y → x ∷ y) rec

  replicate-irreversible : ∀ {A : Set} (n : ℕ) (x : A) → reverse (replicate n x) ≡ replicate n x
  replicate-irreversible zero x = PropEq.refl
  replicate-irreversible (suc n) x with (replicate-irreversible n x) | unfold-reverse x (replicate n x)
  ... | rec | unf-rev = PropEq.trans unf-rev (PropEq.trans (PropEq.cong (λ y → y ++ [ x ]) rec) (replicate-side-irrelevant n x))  


  toʳ : ∀ {a b} → a ≈ b → reverse a ≈ʳ reverse b
  toʳ .{l ++ 0× n} .{_} (equiv n m l) 
          = PropEq.subst (λ x → x ≈ʳ reverse (l ++ 0× m)) (PropEq.sym (reverse-++-commute l (0× n)))
            (PropEq.subst (λ x → reverse (0× n) ++ reverse l ≈ʳ x) (PropEq.sym (reverse-++-commute l (0× m))) 
            (PropEq.subst₂ (λ x y → x ++ reverse l ≈ʳ y ++ reverse l)
                    ( PropEq.sym (replicate-irreversible n zero))
                    ( PropEq.sym (replicate-irreversible m zero)) 
                    ( equiv n m (reverse l))))


  fromʳ' : ∀ {a b} → a ≈ʳ b → reverse a ≈ reverse b
  fromʳ' .{_} .{_} (equiv n m l) = 
     PropEq.subst₂ _≈_ (PropEq.sym (reverse-++-commute (0× n)  l))  (PropEq.sym (reverse-++-commute (0× m) l))
     (PropEq.subst₂ (λ x y → reverse l ++ x ≈ reverse l ++ y)
                ( PropEq.sym (replicate-irreversible n zero))
                ( PropEq.sym (replicate-irreversible m zero))
                 (equiv n m (reverse l))) 

  reverse-reverse-id : ∀ {A : Set} (x : List A) → reverse (reverse x) ≡ x
  reverse-reverse-id [] = PropEq.refl
  reverse-reverse-id (a ∷ b) 
       rewrite
         (unfold-reverse a b)
       | reverse-++-commute (reverse b) [ a ]
       = PropEq.cong (_∷_ a) (reverse-reverse-id b)

  kojo : ∀ {a b} → reverse (reverse a) ≈ reverse (reverse b) → a ≈ b
  kojo {a} {b} eq rewrite reverse-reverse-id a | reverse-reverse-id b = eq

  fromʳ : ∀ {a b} → reverse a ≈ʳ reverse b → a ≈ b
  fromʳ eq = kojo (fromʳ' eq)


  []-identityʳ : ∀ l → l ++ [] ≡ l
  []-identityʳ = proj₂ identity
   where
    open Monoid (Data.List.monoid Bit) using (identity)

  ++-assoc = assoc where
    open Monoid (Data.List.monoid Bit) using (assoc)

  ≈-sym : Symmetric _≈_
  ≈-sym (equiv n m l) = equiv m n l

  ≈ʳ-sym : Symmetric _≈ʳ_
  ≈ʳ-sym (equiv n m l) = equiv m n l

  equivˡ : ∀ n l → l ++ 0× n ≈ l
  equivˡ n l = PropEq.subst ( λ x → l ++ 0× n ≈ x) ([]-identityʳ l) (equiv n 0 l)

  equivʳ : ∀ n l → l ≈ l ++ 0× n
  equivʳ n l = ≈-sym (equivˡ n l)

  ≈-refl : Reflexive _≈_
  ≈-refl {x} =  PropEq.subst (λ x → x ≈ x) ([]-identityʳ x) (equiv 0 0 x) 

  ≈ʳ-refl : Reflexive _≈ʳ_
  ≈ʳ-refl {x} =  equiv 0 0 x

  patternMatch : ∀ {A : Set} (P : A → Set) {x} → P x → ∃ λ z → P z × x ≡ z
  patternMatch _ {x = x} px = (x , (px , PropEq.refl))

  pm : ∀ {x y} → x ≈ y → ∃ λ z → z ≈ y × x ≡ z
  pm = patternMatch _ -- (equiv a b l) = (l ++ 0× a , (equiv a b l , PropEq.refl))

  removeZeroesˡ : ∀ l₀ l₁ a → l₀ ++ 0× a ≡ l₁ → l₀ ≈ l₁
  removeZeroesˡ l₀ l₁ a eq = PropEq.subst (λ x → l₀ ≈ x) eq (equivʳ a l₀)

  open PropEq using (Inspect; inspect; _with-≡_)

  open import Data.Nat using (_+_)

  open import Data.Sum

  removeTooMuch : ∀ a b {l₁ l₂} → (0× a ++ l₁ ≡ 0× b ++ l₂) → (∃ λ c → l₁ ≡ 0× c ++ l₂) ⊎ (∃ λ c → 0× c ++ l₁ ≡ l₂)
  removeTooMuch zero b eq = inj₁ (b , eq)
  removeTooMuch a zero eq = inj₂ (a , eq)
  removeTooMuch (suc a) (suc b) {l₁} {l₂} eq with replicate a zero ++ l₁ | removeTooMuch a b {l₁} {l₂}
  removeTooMuch (suc a) (suc b) {l₁} {l₂} PropEq.refl | .(replicate b zero ++ l₂) | rec = rec PropEq.refl

  replicate-+-distrib : ∀ {A : Set} a b {x : A} → replicate a x ++ replicate b x ≡ replicate (a + b) x
  replicate-+-distrib zero b = PropEq.refl
  replicate-+-distrib (suc a) b {x} with replicate-+-distrib a b
  ... | rec = PropEq.cong (λ y → x ∷ y) rec

  trans+ : ∀ a c b l → 0× c ++ l ≈ʳ 0× a ++ 0× b ++ l
  trans+ a c b l with (++-assoc (0× a) (0× b) l)
  ... | comm rewrite (PropEq.sym comm) = 
               PropEq.subst
                   (λ y → 0× c ++ l ≈ʳ y ++ l) 
                   (PropEq.sym (replicate-+-distrib a b {zero}))
                   (equiv c (a + b) l)

  removeZeroesˡ'' : ∀ {l₀ l₁} a → 0× a ++ l₀ ≈ʳ l₁ → l₀ ≈ʳ l₁
  removeZeroesˡ'' {l₀} {l₁} a eq with inspect (0× a ++ l₀)
  removeZeroesˡ'' {l₀} {l₁} a eq | y with-≡ ≡ rewrite ≡ with eq
  removeZeroesˡ'' {l₀} .{_} a eq | .(replicate b zero ++ l) with-≡ ≡ | equiv b c l with removeTooMuch a b ≡
  ... | inj₁ (b' , l₀≡b'++l) rewrite l₀≡b'++l = equiv b' c l
  ... | inj₂ (a' , a'++l₀≡l) rewrite PropEq.sym a'++l₀≡l  = trans+ c zero a' l₀

  removeZeroesʳ'' : ∀ {l₀ l₁} b → l₀ ≈ʳ 0× b ++ l₁ → l₀ ≈ʳ l₁
  removeZeroesʳ'' b eq = ≈ʳ-sym (removeZeroesˡ'' b (≈ʳ-sym eq))

  removeZeroes : ∀ l₀ l₁ a b → 0× a ++ l₀ ≈ʳ 0× b ++ l₁ → l₀ ≈ʳ l₁
  removeZeroes l₀ l₁ a b eq = removeZeroesˡ'' a (removeZeroesʳ'' b eq)

  addZeroesˡ : ∀ a {l₀ l₁} → l₀ ≈ʳ l₁ → 0× a ++ l₀ ≈ʳ l₁
  addZeroesˡ a (equiv c d l) = ≈ʳ-sym (trans+ a d c l)

  addZeroes : ∀ a b {l₀ l₁} → l₀ ≈ʳ l₁ → 0× a ++ l₀ ≈ʳ 0× b ++ l₁
  addZeroes a b eq = addZeroesˡ a (≈ʳ-sym (addZeroesˡ b (≈ʳ-sym eq)))

  ≡→≈ʳ : ∀ {x y} → x ≡ y → x ≈ʳ y
  ≡→≈ʳ {x} .{x} PropEq.refl = ≈ʳ-refl {x}

  ≡→≈ : ∀ {x y} → x ≡ y → x ≈ y
  ≡→≈ {x} .{x} PropEq.refl = ≈-refl {x}

  ≈ʳ-trans : Transitive _≈ʳ_
  ≈ʳ-trans .{_} .{_} {l3} (equiv a b l₀) eq2 with patternMatch (\y → y ≈ʳ l3) eq2
  ≈ʳ-trans .{_} .{_} .{_} (equiv a b l₀) eq2 | (._ , (equiv c d l₁ , l2≡)) = addZeroes a d l₀≈l₁
   where
    l₀≈l₁ : l₀ ≈ʳ l₁
    l₀≈l₁ = removeZeroes l₀ l₁ b c (≡→≈ʳ l2≡)

  ≈-trans : Transitive _≈_
  ≈-trans {a} {b} {c} ≈₁ ≈₂ = fromʳ (≈ʳ-trans (toʳ ≈₁) (toʳ ≈₂))

  isEquivalence : IsEquivalence _≈_
  isEquivalence = record
    { refl = ≈-refl
    ; trans = ≈-trans
    ; sym = ≈-sym
    }

  setoid : Setoid ₀ ₀
  setoid = record {isEquivalence = isEquivalence}

  open import Data.Digit

  toℕ : List Bit → ℕ
  toℕ = fromDigits

  open import Function using (_∘_; _⟨_⟩_)
  fromℕ : ℕ → List Bit
  fromℕ = theDigits 2

  ℕ-setoid = PropEq.setoid ℕ

  open import Function using (id)
  open import Function.Bijection using (Bijection; Bijective)
  open import Function.Equality using (_⟶_)

  zeroIsZero : ∀ n → fromDigits (0× n) ≡ 0
  zeroIsZero zero = PropEq.refl
  zeroIsZero (suc n) rewrite zeroIsZero n = PropEq.refl

  toℕ-cong : ∀ {x y} → x ≈ y → toℕ x ≡ toℕ y
  toℕ-cong (equiv a b []) rewrite zeroIsZero a | zeroIsZero b = PropEq.refl
  toℕ-cong (equiv a b (h ∷ t)) rewrite toℕ-cong (equiv a b t) = PropEq.refl

  fromℕ⟶ : ℕ-setoid ⟶ setoid
  fromℕ⟶ = record
    { _⟨$⟩_ = fromℕ
    ; cong = λ eq → ≡→≈ (PropEq.cong fromℕ eq)
    }

  toℕ⟶ : setoid ⟶ ℕ-setoid
  toℕ⟶ = record
    { _⟨$⟩_ = toℕ
    ; cong = toℕ-cong
    }

  fromℕ-inj : ∀ {x y} → fromℕ x ≈ fromℕ y → x ≡ y
  fromℕ-inj {x} {y} eq with toDigits 2 x | toDigits 2 y
  fromℕ-inj .{_} .{_} eq | digits xDig | digits yDig = toℕ-cong eq

  open import Data.Nat.DivMod

  bitToℕ : Bit → ℕ
  bitToℕ = Data.Fin.toℕ
 
  open Data.Nat using (_*_)

  suc-inj : ∀ {x y : ℕ} → Data.Nat.suc x ≡ Data.Nat.suc y → x ≡ y
  suc-inj {x} .{x} PropEq.refl = PropEq.refl
  
  suc-inj-fin : ∀ {base : ℕ} → {x y : Fin base} → Data.Fin.suc x ≡ suc y → x ≡ y
  suc-inj-fin {base} {x} .{x} PropEq.refl = PropEq.refl
  

  module DigitInj where
    open import Relation.Binary using (StrictTotalOrder; module StrictTotalOrder)
    open Data.Nat.≤-Reasoning
    open Data.Nat using (_<_; _≤_; s≤s)
    open import Data.Nat.Properties using (isCommutativeSemiring)
    open import Algebra.Structures

    open IsCommutativeSemiring isCommutativeSemiring hiding (zero)

    open import Relation.Nullary

    1+b+c>b : ∀ b c → ¬ 1 + b + c ≤ b
    1+b+c>b zero zero ()
    1+b+c>b (suc b) c (s≤s ≤) = 1+b+c>b b c ≤
    1+b+c>b zero c ()

    +-inj₁ : ∀ c {a b} → c + a ≡ c + b → a ≡ b
    +-inj₁ zero eq = eq
    +-inj₁ (suc c) {a} {b} eq = +-inj₁ c {a} {b} (suc-inj eq)

    open import Data.Empty

    digit-inj₁ : ∀ {base : ℕ} 
              (h : ℕ) → (h < base) 
              → (t₁ t₂ : ℕ)
              → t₁ * base ≡ h + t₂ * base
              → 0 ≡ h
    digit-inj₁ zero _ _ _ _ = PropEq.refl
    digit-inj₁ {suc b'} h h<b zero zero eq = PropEq.trans eq (sym (+-comm 0 h))
    digit-inj₁ {b} h h<b (suc n) zero eq rewrite (PropEq.trans (+-comm 0 h) (PropEq.sym eq)) =  ⊥-elim (1+b+c>b b (n * b) h<b)
    digit-inj₁ {zero} _ () _ _ eq
    digit-inj₁ {suc b'} (suc h) h<b zero (suc n) ()
    digit-inj₁ {b} h h<b (suc m) (suc n) eq = digit-inj₁ h h<b m n eq' where
      module P = PropEq
      eq' : m * b ≡ h + n * b
      eq' =  +-inj₁ b ( P.trans eq (P.trans (P.sym (+-assoc h b (n * b)))
                            (P.trans (P.cong (λ y → y + n * b) (+-comm h b)) (+-assoc b h (n * b)))))

    <-to-≤ : ∀ {a b} → a < b → a ≤ b
    <-to-≤ {zero} a<b = Data.Nat.z≤n
    <-to-≤ {suc n} (s≤s leq) = s≤s (<-to-≤ {n} leq)

    digit-inj₁' : ∀ {base : ℕ} 
              (h₁ h₂ : ℕ) → (h₁ < base) → (h₂ < base)
              → (t₁ t₂ : ℕ)
              → h₁ + t₁ * base ≡ h₂ + t₂ * base
              → h₁ ≡ h₂
    digit-inj₁' h zero h<b _ t1 t2 eq = PropEq.sym (digit-inj₁ h h<b t2 t1 (PropEq.sym eq))
    digit-inj₁' zero h _ h<b t1 t2 eq = digit-inj₁ h h<b t1 t2 eq
    digit-inj₁' {suc b} (suc h₁) (suc h₂) h₁<b h₂<b t1 t2 eq = PropEq.cong suc (digit-inj₁' {suc b} h₁ h₂ ( <-to-≤ h₁<b) (<-to-≤  h₂<b) t1 t2 (suc-inj eq))
    digit-inj₁' {zero} _ _ () () _ _ _

    finToℕ-inj : ∀ {base : ℕ} → {h₁ h₂ : Fin base} → finToℕ h₁ ≡ finToℕ h₂ → h₁ ≡ h₂
    finToℕ-inj {zero} {()} eq
    finToℕ-inj {suc b} {zero} {zero} eq = PropEq.refl
    finToℕ-inj {suc b} {suc h₁} {zero} ()
    finToℕ-inj {suc b} {zero} {suc h₂} ()
    finToℕ-inj {suc b} {suc h₁} {suc h₂} eq = PropEq.cong suc (finToℕ-inj {b} {h₁} {h₂} (suc-inj eq))

    fin<base : ∀ {base : ℕ} → (n : Fin base) → finToℕ n < base
    fin<base zero = s≤s Data.Nat.z≤n
    fin<base (suc n) = s≤s (fin<base n)

    *-inj₂ : ∀ {a b} c → ¬ c ≡ 0 → a * c ≡ b * c → a ≡ b
    *-inj₂ zero nonzero _ = ⊥-elim (nonzero PropEq.refl)
    *-inj₂ {zero} {zero} _ _ _ = PropEq.refl
    *-inj₂ {suc a} {zero} (suc c) _ ()
    *-inj₂ {zero} {suc b} (suc c) _ ()
    *-inj₂ {suc a} {suc b} (suc c) _ eq with *-inj₂ {a} {b} (suc c) (λ ()) (+-inj₁ (suc c) eq)
    ... | rec =  PropEq.cong suc rec

    digit-inj₁'' : ∀ {base : ℕ}
                (h₁ h₂ : Fin base)
                → (t₁ t₂ : ℕ)
                → finToℕ h₁ + t₁ * base ≡ finToℕ h₂ + t₂ * base
                → h₁ ≡ h₂ × t₁ ≡ t₂
    digit-inj₁'' {b} h₁ h₂ t₁ t₂ eq with (digit-inj₁' (finToℕ h₁) (finToℕ h₂) (fin<base h₁) (fin<base h₂) t₁ t₂ eq)
    ... | h2n-eq = finToℕ-inj h2n-eq ,  t-eq where
      bnz : ¬ b ≡ 0
      bnz with b | h₁
      ... | 0 | ()
      ... | suc n | _ = λ ()
      t-eq : t₁ ≡ t₂
      t-eq with eq
      ... | eqq rewrite h2n-eq =  *-inj₂ b bnz (+-inj₁ (finToℕ h₂) eqq)


  digit-inj : ∀ {base : ℕ} (h₁ h₂ : Fin base) (t₁ t₂ : ℕ)
              →   finToℕ h₁ + t₁ * base
                ≡ finToℕ h₂ + t₂ * base
              → h₁ ≡ h₂ × t₁ ≡ t₂
  digit-inj = DigitInj.digit-inj₁''

  ∷-inj-≡ : ∀ {A : Set} {h₁ h₂ : A} {t₁ t₂} 
            → h₁ ∷ t₁ ≡ h₂ ∷ t₂ → h₁ ≡ h₂ × t₁ ≡ t₂
  ∷-inj-≡ PropEq.refl = PropEq.refl , PropEq.refl

  ∷-inj-≡₁ : ∀ {A : Set} {h₁ h₂ : A} {t₁ t₂} 
            → h₁ ∷ t₁ ≡ h₂ ∷ t₂ → h₁ ≡ h₂
  ∷-inj-≡₁ = proj₁ ∘ ∷-inj-≡

  []-∷-inj : ∀ {h t} → h ∷ t ≈ [] → h ≡ zero × t ≈ []
  []-∷-inj eq with patternMatch (λ x → x ≈ []) eq
  ... | l , (pmd1 , eq1) with patternMatch (λ x → l ≈ x) pmd1
  []-∷-inj {h} {t} eq | ._ , (pmd1 , ()) | ._ , (equiv zero zero [] , _)
  []-∷-inj .{zero} .{replicate a zero} eq | ._ , (pmd1 , PropEq.refl) | ._ , (equiv (suc a) zero [] , _) 
         = PropEq.refl , equiv a zero []
  []-∷-inj {h} {t} eq | ._ , (pmd1 , eq₀) | ._ , (equiv a (suc b) [] , ())
  []-∷-inj {h} {t} eq | ._ , (pmd1 , eq₀) | ._ , (equiv a b (hl ∷ tl) , ())

  ∷-inj : ∀ {h₁ h₂ t₁ t₂} → h₁ ∷ t₁ ≈ h₂ ∷ t₂ → h₁ ≡ h₂ × t₁ ≈ t₂
  ∷-inj {h₁} {_} {t₁} eq with patternMatch (λ x → h₁ ∷ t₁ ≈ x) eq
  ∷-inj eq | l₂ , (pmd1 , eq2) with patternMatch (λ x → x ≈ l₂) pmd1
  ∷-inj eq | ._ , (pmd1 , eq2)  | ._ , (equiv zero zero _ , eq1)
      = pmap id ≡→≈ (∷-inj-≡ (eq1 ⟨ PropEq.trans ⟩ (PropEq.sym eq2)))
  ∷-inj .{h} .{h} .{t ++ replicate a zero} .{t ++ replicate b zero} eq | ._ , (pmd1 , PropEq.refl)  | ._ , (equiv a b (h ∷ t) , PropEq.refl) 
     = PropEq.refl , (equiv a b t)
  ∷-inj eq | ._ , (pmd1 , eq2)  | ._ , (equiv zero (suc b) [] , ())
  ∷-inj eq | ._ , (pmd1 , ())  | ._ , (equiv (suc a) zero [] , _)
  ∷-inj .{zero} .{zero} .{replicate a zero} .{replicate b zero} eq | ._ , (pmd1 , PropEq.refl)  | ._ , (equiv (suc a) (suc b) [] , PropEq.refl) = PropEq.refl , equiv a b []


  ∷-cong : ∀ {h₁ h₂ t₁ t₂} → h₁ ≡ h₂ → t₁ ≈ t₂ → h₁ ∷ t₁ ≈ h₂ ∷ t₂
  ∷-cong {h} PropEq.refl (equiv a b l) = equiv a b (h ∷ l)
  
  []-∷-cong : ∀ {h t} → zero ≡ h → [] ≈ t → [] ≈ h ∷ t
  []-∷-cong .{zero} {t} PropEq.refl eq with patternMatch (λ x → x ≈ t) eq
  []-∷-cong .{zero} .{replicate b zero} PropEq.refl _
       | ._ , (equiv 0 b [] , ≡) = equiv 0 (suc b) []
  []-∷-cong .{zero} .{_} PropEq.refl _ | ._ , (equiv (suc a) b [] , ())
  []-∷-cong .{zero} .{_} PropEq.refl _ | ._ , (equiv a b (h ∷ t) , ())

  smaller-toℕ-inj : ∀ {h t} → (0 ≡ fromDigits t → [] ≈ t) 
                    → 0 ≡ finToℕ h + fromDigits t * 2
                    → [] ≈ h ∷ t
  smaller-toℕ-inj {h} {t} rec eq with digit-inj zero h 0 (fromDigits t) eq
  ... | 0≡h , []≡ft = []-∷-cong 0≡h (rec []≡ft)

  toℕ-inj : ∀ {x y} → toℕ x ≡ toℕ y → x ≈ y
  toℕ-inj {h₁ ∷ t₁} {h₂ ∷ t₂} eq with toℕ-inj {t₁} {t₂}
  ... | rec with digit-inj h₁ h₂ (fromDigits t₁) (fromDigits t₂) eq 
  ... | h₁≡h₂ , t₁≡t₂ = ∷-cong h₁≡h₂ (rec t₁≡t₂)
  toℕ-inj {[]} {h ∷ t} eq with toℕ-inj {[]} {t}
  ... | rec = smaller-toℕ-inj rec eq
  toℕ-inj {h ∷ t} {[]} eq with toℕ-inj {[]} {t}
  ... | rec = ≈-sym (smaller-toℕ-inj rec (PropEq.sym eq))
  toℕ-inj {[]} {[]} eq = equiv 0 0 []

  toFromℕ-inverse : ∀ x → toℕ (fromℕ x) ≡ x
  toFromℕ-inverse x with (toDigits 2 x)
  toFromℕ-inverse .(fromDigits dig) | digits dig = PropEq.refl

  bijective : Bijective toℕ⟶
  bijective = record
    { injective = toℕ-inj
    ; surjective = record 
       { from = fromℕ⟶
       ; right-inverse-of = toFromℕ-inverse
       }
    }

  bijection-to-ℕ : Bijection setoid ℕ-setoid
  bijection-to-ℕ = record { bijective = bijective }
