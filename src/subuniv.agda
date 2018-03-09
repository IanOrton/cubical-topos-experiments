{-# OPTIONS --type-in-type #-}

open import Agda.Primitive public

open import prelude public
open import impredicative public

data Unit₁ : Set₁ where
  tt : Unit₁

postulate
  -- Assume that we have some property, P, of families
  P  :
    {Γ : Set₁}
    → --------------
    (Γ → Set) → Set
  -- Assume that P is functorial 
  P' :
    {Δ Γ : Set₁}
    {A : Γ → Set}
    (f : Δ → Γ)
    → --------------
    P A → P (A ∘ f)

-- Then define the family of families with the P property
PFam : Set₁ → Set₁
PFam Γ = Σ A ∈ (Γ → Set) , P A

-- This is also functorial
PFam' :
  {Δ Γ : Set₁}
  (f : Δ → Γ)
  → --------------
  PFam Γ → PFam Δ
PFam' f (A , p) = (A ∘ f , P' f p)
  
-- Postulate a generic universe of P-families
postulate
  U  : Set₁
  El : PFam U

El* : {Γ : Set₁} → (Γ → U) → PFam Γ
El* f = PFam' f El

postulate
  code : {Γ : Set₁}(A : PFam Γ) → prf (∃ a ∈ (Γ → U) , PFam' a El ≈ A)
  --code-el : {Γ : Set₁}(A : PFam Γ) → prf ∥ PFam' (code A) El ≡ A ∥

-- code' : {Γ : Set₁}(A : PFam Γ) → Γ → U
-- code' A = fst (axd (λ a → PFam' a El ≈ A) (code A))

-- code-el : {Γ : Set₁}(A : PFam Γ) → PFam' (code' A) El ≡ A
-- code-el A = let rr = snd (axd (λ a → PFam' a El ≈ A) (code A)) in rr

-- code-el' : {Γ : Set₁}(A : PFam Γ) → PFam' (code A) El ≡ A
-- code-el' A = ∥∥-elim (λ z → z) uip (code-el A)

Extensionality = {A B : Set₁}{f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

-- Say a family has P-fibres if all its fibres, viewed as
-- families over Unit, have the P property
PFib :
  {Γ : Set₁}
  → --------------
  (Γ → Set) → Set₁
PFib {Γ} A = (x : Γ) → P {Γ = Unit₁} (λ _ → A x)

lemma : {A B : Set} → (A → prf ∥ B ∥) → prf ∥ (A → B) ∥
lemma f = {!!}

lemma' : {A B : Set} → prf ∥ (A → B) ∥ → (A → prf ∥ B ∥)
lemma' {A} {B} f a = ∥∥-rec ∥ B ∥ (λ f → ∣ f a ∣) f

-- Assuming extensionality at level 1 then if a
-- family has P-fibres then it is a P-family
PFib→PFam :
  {Γ : Set₁}
  (A : Γ → Set)
  (funext : Extensionality)
  → --------------
  PFib A → prf ∥ P A ∥
PFib→PFam {Γ} A funext pFib = ∥∥-elim {!!} {!!} (code {!!}) where
  AU : Γ → prf (∃ Ax ∈ U , {!!})
  AU x = ∥∥-elim {!!} {!!} (code ((λ _ → A x) , pFib x))
--   AU=A : (fst El) ∘ AU ≡ A
--   AU=A = funext (λ x → let r = code-el (((λ _ → A x)) , pFib x) in {!!})
--  APFam : prf ∥ PFam Γ ∥
--  APFam = ∥∥-rec ∥ PFam Γ ∥ (λ A → ∣ El* A ∣) AUex --PFam' AU El
--  proj₁APFam=A : fst APFam ≡ A
--  proj₁APFam=A = {!!} -- funext (λ x → cong (λ pfam → proj₁ pfam tt) (code-el ((λ _ → A x) , pFib x)))

-- MerelySurj : {A B : Set₁} → (A → B) → Ω
-- MerelySurj {A} {B} f = All b ∈ B , ∃ a ∈ A , f a ≈ b

-- postulate
--   msEL* : ∀{Γ} → prf (MerelySurj (El* {Γ}))
--   --code : {Γ : Set₁}(A : PFam Γ) → Γ → U
--   --code-el : {Γ : Set₁}(A : PFam Γ) → PFam' (code A) El ≡ A

-- Extensionality = {A B : Set₁}{f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

-- -- Say a family has P-fibres if all its fibres, viewed as
-- -- families over Unit, have the P property
-- PFib :
--   {Γ : Set₁}
--   → --------------
--   (Γ → Set) → Set₁
-- PFib {Γ} A = (x : Γ) → P {Γ = Unit₁} (λ _ → A x)

-- lemma : {A B : Set} → (A → prf ∥ B ∥) → prf ∥ (A → B) ∥
-- lemma f = {!!}

-- lemma' : {A B : Set} → prf ∥ (A → B) ∥ → (A → prf ∥ B ∥)
-- lemma' {A} {B} f a = ∥∥-rec ∥ B ∥ (λ f → ∣ f a ∣) f

-- -- Assuming extensionality at level 1 then if a
-- -- family has P-fibres then it is a P-family
-- PFib→PFam :
--   {Γ : Set₁}
--   (A : Γ → Set)
--   (funext : Extensionality)
--   → --------------
--   PFib A → prf ∥ P A ∥
-- PFib→PFam {Γ} A funext pFib = subst (λ A → prf ∥ P A ∥) {!!} {!APFam!} where
--   AU : Γ → prf ∥ U ∥
--   AU x = ∥∥-rec ∥ U ∥ (λ A → ∣ fst A tt ∣) (msEL* ((λ _ → A x) , pFib x))
--   AU' : prf ∥ (Γ → U) ∥
--   AU' P u = u (λ x → ∥∥-elim (λ z → z) {!!} (AU x))
--   AUex : prf (∃ A' ∈ (Γ → U) , fst El ∘ A' ≈ A)
--   AUex = {!!}
-- --  APFam : prf ∥ PFam Γ ∥
-- --  APFam = ∥∥-rec ∥ PFam Γ ∥ (λ A → ∣ El* A ∣) AUex --PFam' AU El
-- --  proj₁APFam=A : fst APFam ≡ A
-- --  proj₁APFam=A = {!!} -- funext (λ x → cong (λ pfam → proj₁ pfam tt) (code-el ((λ _ → A x) , pFib x)))

