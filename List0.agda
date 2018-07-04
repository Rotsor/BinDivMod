module List0 where

open import Level            using (_⊔_)
open import Function         using (id; _∘_; _$_; case_of_; const)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Unary   using (Decidable)
open import Relation.Binary  using (Reflexive; Setoid)
open import Relation.Binary.PropositionalEquality as PE using 
                                         (_≡_; _≗_; cong; cong₂; refl; sym)
open PE.≡-Reasoning 
open import Data.Empty   using (⊥-elim)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _∷ʳ_; [_]; _++_; reverse; length;
                                                             replicate; map) 
open import Data.List.Properties using (length-++; reverse-involutive)
open import Data.List.All using (All) renaming ([] to []a; _∷_ to _∷a_)
open import Data.List.All.Properties using (All¬⇒¬Any)
open import Data.List.Any            using (Any)
import Data.List.Membership.Setoid as Membership 
open import Data.String as Str  using (String) renaming (_++_ to _+s+_)
open import Data.Nat            using (ℕ; suc; _+_) 
open import Data.Nat.Properties using (+-comm) 



--****************************************************************************
concatStr : List String → String
concatStr []           = ""
concatStr (str ∷ strs) = str +s+ (concatStr strs)

pairs :  ∀ {α β} {A : Set α} {B : Set β} → List A → List B → List (A × B)
pairs []       _  =  []   
pairs (x ∷ xs) ys =  (map (_,_ x) ys) ++ (pairs xs ys)

test :  length (pairs (1 ∷ 2 ∷ []) (1 ∷ 2 ∷ 3 ∷ [])) ≡ 6
test =  refl


all-map-const : ∀ {α β} {A : Set α} {B : Set β} → (y : B) → (xs : List A) →
                                                All (_≡ y) (map (const y) xs) 
all-map-const _ []       =  []a
all-map-const y (_ ∷ xs) =  refl ∷a (all-map-const y xs)

all-xs=c→map-c-xs≡xs : ∀ {α} {A : Set α} → (c : A) → {xs : List A} → 
                                        All (_≡ c) xs → map (const c) xs ≡ xs

all-xs=c→map-c-xs≡xs _ {[]}     _             =  refl
all-xs=c→map-c-xs≡xs c {x ∷ xs} (x≡c ∷a xs=c) =  
                             cong₂ _∷_ (sym x≡c) (all-xs=c→map-c-xs≡xs c xs=c) 

all≡in-replicate :  ∀ {α}{A : Set α} → (n : ℕ) → (x : A) →
                                                 All (_≡ x) (replicate n x)
all≡in-replicate 0       _ =  []a
all≡in-replicate (suc n) x =  refl ∷a (all≡in-replicate n x)

map-replicate :  ∀ {α β} {A : Set α} {B : Set β} → 
                                    (f : A → B) → (n : ℕ) → (x : A) → 
                                    map f (replicate n x) ≡ replicate n (f x)
map-replicate _ 0       _ =  refl
map-replicate f (suc n) x =  cong ((f x) ∷_) (map-replicate f n x)


length-xs:x :  ∀ {α} {A : Set α} → (x : A) → (xs : List A) → 
                                            length (xs ∷ʳ x) ≡ suc (length xs)
length-xs:x x xs = 
                 begin length (xs ∷ʳ x)   ≡⟨ length-++ xs ⟩
                       (length xs) + 1    ≡⟨ +-comm (length xs) 1 ⟩
                       suc (length xs)
                 ∎

tail0 :  ∀ {α} {A : Set α} → List A → List A   
tail0 []       = []
tail0 (_ ∷ bs) = bs

++[] :  ∀ {α} {A : Set α} → (_++ []) ≗ id {A = List A}
++[] []       =  refl
++[] (x ∷ xs) =  cong (x ∷_) (++[] xs)


reverse-injective-≡ :  ∀ {α} {A : Set α} {xs ys : List A} → 
                                           reverse xs ≡ reverse ys → xs ≡ ys
reverse-injective-≡ {α} {A} {xs} {ys} rev-xs≡rev-ys = 
                  begin
                    xs                     ≡⟨ sym (reverse-involutive xs) ⟩
                    reverse (reverse xs)   ≡⟨ cong reverse rev-xs≡rev-ys ⟩
                    reverse (reverse ys)   ≡⟨ reverse-involutive ys ⟩
                    ys
                  ∎

replicate-m+n :  ∀ {α} {A : Set α} → (m n : ℕ) → (x : A) → 
                      replicate (m + n) x ≡ (replicate m x) ++ (replicate n x)
replicate-m+n 0       _ _ = refl
replicate-m+n (suc m) n x = 
  begin 
    replicate (suc m + n) x               ≡⟨ refl ⟩
    x ∷ replicate (m + n) x               ≡⟨ cong (x ∷_) (replicate-m+n m n x)
                                           ⟩
    x ∷ (replicate m x ++ replicate n x)       ≡⟨ refl ⟩
    (x ∷ (replicate m x)) ++ (replicate n x)   ≡⟨ refl ⟩
    replicate (suc m) x ++ replicate n x
  ∎

------------------------------------------------------------------------------
module _ {α} {A : Set α}
  where
  data Null : List A → Set α  where  isNull : Null []    

  null⇒≡[] :  {xs : List A} → Null xs → xs ≡ []
  null⇒≡[] isNull =  refl

  null? :  (xs : List A) → Dec (Null xs)
  null? []      = yes isNull
  null? (_ ∷ _) = no λ()


------------------------------------------------------------------------------
module _ {α} (A : Set α) 
  where
  setoid = PE.setoid A
  open Membership setoid using (_∉_)

  ∉[] :  {x : A} → x ∉ []
  ∉[] ()


  record Found {p} {P : A → Set p} (P? : Decidable P) (xs : List A) :
                                                                 Set (α ⊔ p)
         where
         constructor found′

         field  prefix   : List A
                found    : A
                suffix   : List A
                ¬prefix  : All (¬_ ∘ P) prefix
                P-found  : P found
                concatEq : prefix ++ (found ∷ suffix) ≡ xs

  Search :  ∀ {p} {P : A → Set p} → Decidable P → List A →  Set (α ⊔ p)
  Search {_} {P} P? xs =
                       Found P? xs ⊎ All (¬_ ∘ P) xs

  open Found

  ----------------------------------------------------------------------------
  search : ∀ {p} {P : A → Set p} → (P? : Decidable P) → (xs : List A) →
                                                              Search P? xs
  search _  []       =  inj₂ []a
  search P? (x ∷ xs) =
         case P? x
         of \
         { (yes Px) → inj₁ $ record{ prefix   = []
                                   ; found    = x
                                   ; suffix   = xs
                                   ; ¬prefix  = []a
                                   ; P-found  = Px
                                   ; concatEq = refl }
         ; (no ¬Px) →
               case search P? xs
               of \
               { (inj₂ ¬xs) → inj₂ (¬Px ∷a ¬xs)
               ; (inj₁ fnd) →
                       let y = found fnd

                           e :  (prefix fnd) ++ (y ∷ (suffix fnd)) ≡ xs
                           e =  concatEq fnd
                       in
                       inj₁ $ record{ prefix   = x ∷ (prefix fnd)
                                    ; found    = y
                                    ; suffix   = suffix fnd
                                    ; ¬prefix  = ¬Px ∷a (¬prefix fnd)
                                    ; P-found  = P-found fnd
                                    ; concatEq = cong (x ∷_) e }
               }
         }

  ----------------------------------------------------------------------------
  findExisting : ∀ {p} {P : A → Set p} → (P? : Decidable P) → (xs : List A) → 
                                                              Any P xs      → 
                                                              Found P? xs
  findExisting {_} {P} P? xs any-P-xs  with  search P? xs

  ... | inj₁ fnd   = fnd
  ... | inj₂ ¬P-xs = ⊥-elim (¬any-P-xs any-P-xs) 
                     where
                     ¬any-P-xs : ¬ Any P xs
                     ¬any-P-xs = All¬⇒¬Any ¬P-xs