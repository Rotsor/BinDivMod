module NatProp0 where

open import Function using (_∘_; _$_; case_of_)
open import Algebra.FunctionProperties as FuncProp using (Op₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary using (_⇒_; _Preserves_⟶_; Tri; DecTotalOrder; 
                                                       StrictTotalOrder)
open import Relation.Binary.PropositionalEquality as PE 
                            using (_≡_; _≢_; cong; cong₂; subst; 
                                   subst₂; refl; sym; trans)
open PE.≡-Reasoning 
open import Data.Empty   using (⊥-elim)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.List    using (List; []; _∷_)
open import Data.Nat     using (ℕ; _≟_; suc; pred; _+_; _∸_; _*_; _<_; _>_; 
                                   _≤_; s≤s; z≤n; _≰_; _≮_; _≯_; ⌊_/2⌋; _^_)
open import Data.Nat.Properties as NatProp 
     using (+-assoc; +-comm; *-comm; *-assoc; ≤-step; ≤-refl; ≤-reflexive; 
            ≤-trans; ≤-antisym; <-irrefl; <-trans; <-asym; 1+n≰n; n≤1+n; <⇒≤; 
            <⇒≢; pred-mono; m≤m+n; ⌊n/2⌋-mono; +-mono-≤; *-mono-≤; 
            m+n∸m≡n; i^j≡0⇒i≡0; ^-distribˡ-+-*; ≡-decSetoid; 
            module ≤-Reasoning
           )
     renaming (*-distribˡ-+ to lDistrib; *-distribʳ-+ to rDistrib)

open ≤-Reasoning using () renaming (begin_ to ≤begin_; _∎ to _≤end;
                                          _≡⟨_⟩_ to _≡≤[_]_; _≤⟨_⟩_ to _≤[_]_)




--****************************************************************************
-- Auxiliary items needed for the Bin items.

natDTO = NatProp.≤-decTotalOrder
natSTO = NatProp.<-strictTotalOrder

_≤n?_ = DecTotalOrder._≤?_ natDTO

tail0 : ∀ {α} {A : Set α} → List A → List A      -- ≗ drop 1,  but let it be
tail0 []       = []
tail0 (_ ∷ bs) = bs

half : ℕ → ℕ
half = ⌊_/2⌋    -- renaming

open StrictTotalOrder natSTO using (compare; <-resp-≈)

+cong₁ : {y : ℕ} → (_+ y) Preserves _≡_ ⟶ _≡_
+cong₁ {y} =  cong (_+ y)

+cong₂ : {x : ℕ} → (x +_) Preserves _≡_ ⟶ _≡_
+cong₂ {x} =  cong (x +_)

1* : (x : ℕ) → (1 * x) ≡ x
1* x =  +-comm x 0

*1 :  ∀ x  → x * 1 ≡ x
*1 x =  trans (*-comm x 1) (1* x)

n*2≡n+n :  ∀ n → n * 2 ≡ n + n
n*2≡n+n n = 
          begin n * 2          ≡⟨ *-comm n 2 ⟩
                (suc 1 * n)    ≡⟨ refl ⟩
                n + 1 * n      ≡⟨ cong (n +_) (1* n) ⟩
                n + n
          ∎

k+[m+n]≡m+[k+n] :  ∀ k m n → k + (m + n) ≡ m + (k + n)
k+[m+n]≡m+[k+n] k m n = 
                      begin k + (m + n)   ≡⟨ sym (+-assoc k m n) ⟩
                            (k + m) + n   ≡⟨ cong (_+ n) (+-comm k m) ⟩
                            (m + k) + n   ≡⟨ +-assoc m k n ⟩
                            m + (k + n)
                      ∎

k*[m*n]≡m*[k*n] :  ∀ k m n → k * (m * n) ≡ m * (k * n)
k*[m*n]≡m*[k*n] k m n = 
                      begin k * (m * n)   ≡⟨ sym (*-assoc k m n) ⟩
                            (k * m) * n   ≡⟨ cong (_* n) (*-comm k m) ⟩
                            (m * k) * n   ≡⟨ *-assoc m k n ⟩
                            m * (k * n)
                      ∎

[1+m]*n≡m+m*n :  ∀ m n → (suc m) * n ≡ n + m * n
[1+m]*n≡m+m*n m n =  
                  begin (suc m) * n     ≡⟨ rDistrib n 1 m ⟩
                        1 * n + m * n   ≡⟨ cong (_+ (m * n)) (1* n) ⟩
                        n + m * n
                  ∎

[1+m]*n≡n+n*m :  ∀ m n → (suc m) * n ≡ n + n * m
[1+m]*n≡n+n*m m n =  
                  begin (suc m) * n     ≡⟨ rDistrib n 1 m ⟩
                        1 * n + m * n   ≡⟨ cong₂ _+_ (1* n) (*-comm m n) ⟩
                        n + n * m
                  ∎
                           
suc∘pred : ∀ {n} → n > 0 → suc (pred n) ≡ n    -- 1 ≤ n    
suc∘pred {suc _} _  = refl
suc∘pred {0}     ()

pred-n≤n :  ∀ n → pred n ≤ n
pred-n≤n 0       =  z≤n
pred-n≤n (suc n) =  n≤1+n n

0<1+n : ∀ {n} → 0 < suc n
0<1+n = s≤s z≤n

pred< :  ∀ {n} → 0 < n → pred n < n
pred< {suc n} _ =  ≤-refl 
pred< {0} ()

suc≢0 : ∀ {n} → suc n ≢ 0 
suc≢0 ()

≤0⇒≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
≤0⇒≡0 z≤n =  refl

2+n>1 :  ∀ {n} → suc (suc n) > 1  -- 2 ≤ suc suc n
2+n>1 =  s≤s $ s≤s z≤n

≤⇒⊎ : ∀ {m n} → m ≤ n → m < n ⊎ m ≡ n
≤⇒⊎ {0}     {0}     _          =  inj₂ refl
≤⇒⊎ {0}     {suc n} _          =  inj₁ 0<1+n
≤⇒⊎ {suc m} {suc n} (s≤s m≤n)  with  ≤⇒⊎ m≤n
...                            | inj₂ m=n = inj₂ $ cong suc m=n
...                            | inj₁ m<n = inj₁ m''≤n'
                                            where
                                            m' = suc m

                                            m''≤n' : suc m' ≤ suc n
                                            m''≤n' = s≤s m<n
⊎⇒≤ : ∀ {m n} → m < n ⊎ m ≡ n → m ≤ n
⊎⇒≤ (inj₂ m=n) =  ≤-reflexive m=n
⊎⇒≤ (inj₁ m<n) =  ≤-trans m≤m' m<n  where
                                    m≤m' = ≤-step ≤-refl

>⇒≰ : ∀ {m n} → m > n → m ≰ n
>⇒≰ m>n m≤n =  <⇒≢ n<m n=m  where
                            n<m = m>n
                            n≤m = <⇒≤ n<m
                            n=m = ≤-antisym n≤m m≤n

>⇒≢ : ∀ {m n} → m > n → m ≢ n
>⇒≢ {_} {n} m>n =  <⇒≢ m>n ∘ sym

≤⇒≯ : ∀ {m n} → m ≤ n → m ≯ n
≤⇒≯ m≤n m>e =  >⇒≰ m>e m≤n

<⇒≱ : ∀ {m n} → m > n → m ≰ n
<⇒≱ m>n m≤n =  <⇒≢ n<m n=m  where n<m = m>n
                                  n≤m = <⇒≤ n<m
                                  n=m = ≤-antisym n≤m m≤n

≡⇒≯ : ∀ {m n} → m ≡ n → m ≯ n
≡⇒≯ m=n =  ≤⇒≯ (≤-reflexive m=n)

≡⇒≮ : ∀ {m n} → m ≡ n → m ≮ n
≡⇒≮ m=n =  ≡⇒≯ (sym m=n)

≢0⇒> : ∀ {n} → n ≢ 0 → n > 0
≢0⇒> {suc _} _   =  0<1+n
≢0⇒> {0}     0≢0 =  ⊥-elim $ 0≢0 refl

≤,≢-then< : ∀ {m n} → m ≤ n → m ≢ n → m < n
≤,≢-then< m≤n m≢n  with  ≤⇒⊎ m≤n
...              | inj₁ m<n =  m<n
...              | inj₂ m=n =  ⊥-elim $ m≢n m=n

open Tri

≰⇒> : ∀ {m n} → m ≰ n → m > n
≰⇒> {m} {n} m≰n =
                case compare m n of \
                     { (tri> _   _    m>n) → m>n
                     ; (tri< m<n _   _   ) → ⊥-elim $ m≰n $ <⇒≤ m<n
                     ; (tri≈ _   m=n _   ) → ⊥-elim $ m≰n $ ≤-reflexive m=n }

<-antisym : ∀ {m n} → m < n → n ≮ m
<-antisym m<n n<m =  <-irrefl refl $ <-trans m<n n<m

≮0 :  ∀ {n} → n ≮ 0
≮0 {n} n'≤0 =  
            ≤⇒≯ n'≤0 (0<1+n {n})

                 
pred-mono-< :  ∀ {m n} → 0 < m → m < n → pred m < pred n

pred-mono-< {0}     {_}     0<0 _     =  ⊥-elim (<-irrefl refl 0<0)
pred-mono-< {_}     {0}     _   m<0   =  ⊥-elim (≮0 m<0)
pred-mono-< {suc m} {suc n} _   m'<n' =  pred-mono m'<n'

<1⇒≡0 : ∀ {n} → n < 1 → n ≡ 0
<1⇒≡0 {n} =
          ≤0⇒≡0 ∘ pred-mono

m+n≡0⇒both≡0 :  ∀ m n → m + n ≡ 0 →  m ≡ 0 × n ≡ 0

m+n≡0⇒both≡0 0       0       _      =  (refl , refl) 
m+n≡0⇒both≡0 (suc _) _       ()
m+n≡0⇒both≡0 m       (suc n) m+n'≡0 =  ⊥-elim (suc≢0 n'+m≡0)
                                    where
                                    n'+m≡0 = trans (+-comm (suc n) m) m+n'≡0

≤1→0or1 : ∀ n → n ≤ 1 → n ≡ 0 ⊎ n ≡ 1
≤1→0or1 0             _     =  inj₁ refl
≤1→0or1 (suc 0)       _     =  inj₂ refl
≤1→0or1 (suc (suc n)) n''≤1 =  ⊥-elim $ n''≰1 n''≤1
                               where
                               n''≰1 = >⇒≰ $ s≤s $ s≤s z≤n

monot-half : half Preserves _≤_ ⟶ _≤_
monot-half = ⌊n/2⌋-mono

0∸ :  ∀ n → 0 ∸ n ≡ 0
0∸ 0       =  refl
0∸ (suc _) =  refl

∸≡0⇒≤ : ∀ {m n} → m ∸ n ≡ 0 → m ≤ n
∸≡0⇒≤ {0}     {_}     _     =  z≤n
∸≡0⇒≤ {suc m} {0}     ()
∸≡0⇒≤ {suc m} {suc n} m∸n≡0 =  s≤s $ ∸≡0⇒≤ {m} {n} m∸n≡0

≤⇒∸≡0 : ∀ {m n} → m ≤ n → m ∸ n ≡ 0
≤⇒∸≡0 {0}     {n}     _         =  0∸ n
≤⇒∸≡0 {suc m} {suc n} (s≤s m≤n) =  ≤⇒∸≡0 {m} {n} m≤n

m<n⇒0<n∸m :  ∀ {m n} → m < n → 0 < n ∸ m
m<n⇒0<n∸m {m} {n} m<n = 
                      case compare 0 (n ∸ m)
                      of \ 
                      { (tri< lt _     _    ) → lt
                      ; (tri≈ _  0≡n∸m _    ) → let m≤n = ∸≡0⇒≤ (sym 0≡n∸m)
                                                in  ⊥-elim (<⇒≱ m<n m≤n)

                      ; (tri> _  _     0>n∸m) → ⊥-elim (≮0 {n ∸ m} 0>n∸m)
                      }

1≤2^n :  ∀ n → 1 ≤ 2 ^ n
1≤2^n 0       =  ≤-refl
1≤2^n (suc n) =  ≤begin 1              ≤[ s≤s z≤n ]
                        2             ≡≤[ sym (*1 2) ]
                        2 * 1          ≤[ *-mono-≤ (≤-refl {2}) (1≤2^n n) ]
                        2 * (2 ^ n)
                 ≤end

---------------------------------------
2^-mono-≤ :  (2 ^_) Preserves _≤_ ⟶ _≤_
2^-mono-≤ {m} {0} m≤0 =  
                      ≤-reflexive (cong (2 ^_) m≡0)
                      where
                      m≡0 = ≤0⇒≡0 m≤0 

2^-mono-≤ {0} {suc n} _ =  
                    ≤begin 2 ^ 0        ≡≤[ refl ]        
                           1             ≤[ s≤s z≤n ]
                           2            ≡≤[ sym (*1 2) ]
                           2 * 1         ≤[ *-mono-≤ (≤-refl {2}) (1≤2^n n) ]
                           2 * (2 ^ n)
                    ≤end 

2^-mono-≤ {suc m} {suc n} (s≤s m≤n) =  *-mono-≤ (≤-refl {2}) (2^-mono-≤ m≤n)


------------------------------------------------------------------------------
m<n⇒k+m*k≤n*k :  ∀ {m n} k → m < n → k + m * k ≤ n * k
m<n⇒k+m*k≤n*k {m} {n} k m<n = 
                  ≤begin k + m * k       ≡≤[ cong (_+ (m * k)) (sym (1* k)) ] 
                         1 * k + m * k   ≡≤[ sym (rDistrib k 1 m) ] 
                         (1 + m) * k      ≤[ *-mono-≤ m<n ≤-refl ]
                         n * k
                  ≤end

*r-mono-≤ :  ∀ n → (_* n) Preserves _≤_ ⟶ _≤_
*r-mono-≤ n m≤n = 
                *-mono-≤ m≤n (≤-refl {n}) 


suc*-mono-< :  ∀ n → ((suc n) *_) Preserves _<_ ⟶ _<_
suc*-mono-< n {m} {k} m'≤k =
     ≤begin                                   -- goal :  suc (n' * m) ≤ n' * k 
       suc (n' * m)          ≤[ +-mono-≤ (z≤n {n}) suc-n'm≤suc-n'm ]
       n + (1 + n' * m)     ≡≤[ sym $ +-assoc n 1 _ ]
       (n + 1) + n' * m     ≡≤[ cong₂ _+_ (+-comm n 1) (*-comm n' m) ]
       n' + m * n'          ≡≤[ refl ]
       m' * n'              ≡≤[ *-comm m' n' ]
       n' * m'               ≤[ m≤m+n (n' * m') (n' * d) ]
       n' * m' + n' * d     ≡≤[ sym $ lDistrib n' m' d ]
       n' * (m' + d)        ≡≤[ cong (n' *_) m'+d≡k ]
       n' * k
     ≤end
     where n' = suc n
           m' = suc m
           d  = k ∸ m'

           m'+d≡k : m' + d ≡ k    -- m' + (k ∸ m') = ..  
           m'+d≡k = m+n∸m≡n m'≤k

           suc-n'm≤suc-n'm :  suc (n' * m) ≤ suc (n' * m)
           suc-n'm≤suc-n'm =  ≤-refl

*suc-mono-< :  ∀ n → (_* (suc n)) Preserves _<_ ⟶ _<_
*suc-mono-< n {m} {k} m<k =
                          subst₂ _<_ (*-comm n' m) (*-comm n' k) n'*m<n'*k 
                          where
                          n'        = suc n
                          n'*m<n'*k = suc*-mono-< n {m} {k} m<k

------------------------------------------------------------------------------
module FP-Nat = FuncProp (_≡_ {A = ℕ})

*-rDistrib-∸ :  FP-Nat._DistributesOverʳ_ _*_ _∸_
*-rDistrib-∸ =  NatProp.*-distribʳ-∸ 

*-lDistrib-∸ :  FP-Nat._DistributesOverˡ_ _*_ _∸_
*-lDistrib-∸ m n k =
               begin m * (n ∸ k)      ≡⟨ *-comm m (n ∸ k) ⟩
                     (n ∸ k) * m      ≡⟨ *-rDistrib-∸ m n k ⟩
                     n * m ∸ k * m    ≡⟨ cong₂ _∸_ (*-comm n m) (*-comm k m) ⟩
                     m * n ∸ m * k 
               ∎

------------------------------------------------------------------------------
data Even : ℕ → Set where  even0  : Even 0
                           even+2 : {n : ℕ} → Even n → Even (suc $ suc n)
Odd : ℕ → Set
Odd = ¬_ ∘ Even

odd+2 : ∀ {n} → Odd n → Odd (suc (suc n))
odd+2 {0}     odd-0  _                = odd-0 even0
odd+2 {suc n} odd-n' (even+2 even-n') = odd-n' even-n'

odd-suc : ∀ {n} → Even n → Odd (suc n)
odd-suc {0}           _               =  λ ()
                                           -- no constructor for Even (suc 1)
odd-suc {suc (suc n)} (even+2 even-n) =  odd+2 $ odd-suc even-n

even-2* : ∀ n → Even (n * 2)
even-2* 0       =  even0
even-2* (suc n) =  even+2 $ even-2* n


------------------------------------------------------------------------------
half<n*2> : ∀ n → ⌊ (n * 2) /2⌋ ≡ n
half<n*2> 0       =  refl
half<n*2> (suc n) =  cong suc $ half<n*2> n

half<1+n*2> : ∀ n → ⌊ (suc (n * 2)) /2⌋ ≡ n
half<1+n*2> 0       = refl
half<1+n*2> (suc n) =
       begin
         ⌊ (suc ((1 + n) * 2)) /2⌋        ≡⟨ cong ⌊_/2⌋ $ cong suc $
                                                             rDistrib 2 1 n ⟩
         ⌊ (suc (2 + (n * 2))) /2⌋        ≡⟨ refl ⟩
         ⌊ (suc (suc (suc (n * 2)))) /2⌋  ≡⟨ refl ⟩
         suc ⌊ (suc (n * 2)) /2⌋          ≡⟨ cong suc $ half<1+n*2> n ⟩
         suc n
       ∎

half-n*2 : ∀ n → half (n * 2) ≡ n
half-n*2 0       =  refl
half-n*2 (suc n) =  cong suc $ half-n*2 n

half-1+n*2 : ∀ n → half (suc (n * 2)) ≡ n
half-1+n*2 0       = refl
half-1+n*2 (suc n) =
         begin
           half (suc ((1 + n) * 2))        ≡⟨ cong half $ cong suc $
                                                             rDistrib 2 1 n ⟩
           half (suc (2 + (n * 2)))        ≡⟨ refl ⟩
           half (suc (suc (suc (n * 2))))  ≡⟨ refl ⟩
           suc (half (suc (n * 2)))        ≡⟨ cong suc $ half-1+n*2 n ⟩
           suc n
         ∎

open ≤-Reasoning using () renaming (begin_ to ≤begin_; _∎ to _≤end;
                                         _≡⟨_⟩_ to _≡≤[_]_; _≤⟨_⟩_ to _≤[_]_)

half≤ : (n : ℕ) → ⌊ n /2⌋ ≤ n
half≤ 0             = z≤n
half≤ (suc 0)       = z≤n
half≤ (suc (suc n)) = ≤begin  ⌊ (suc (suc n)) /2⌋   ≡≤[ refl ]
                              suc ⌊ n /2⌋            ≤[ s≤s $ half≤ n ]
                              suc n                  ≤[ n≤1+n (suc n) ]
                              suc (suc n)
                      ≤end

half-suc-n≤n : (n : ℕ) → ⌊ (suc n) /2⌋  ≤ n
half-suc-n≤n 0       =  z≤n
half-suc-n≤n (suc n) =  ≤begin  ⌊ (suc (suc n)) /2⌋   ≡≤[ refl ]
                                suc ⌊ n /2⌋            ≤[ s≤s $ half≤ n ]
                                suc n
                        ≤end
