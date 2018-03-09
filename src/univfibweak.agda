
{-# OPTIONS --rewriting --type-in-type #-}
open import Level
open import prelude
open import impredicative
open import interval
open import Data.paths
open import cof
open import fibrations
open import equivs
open import glueing


Fib₀ : Set₁ → Set₁
Fib₀ Γ = Σ A ∈ (Γ → Set) , Fib A

Fib' : {Δ Γ : Set₁}(f : Δ → Γ) → Fib₀ Γ → Fib₀ Δ
Fib' f (A , α) = (A ∘ f , reindex A α f)

-- infix 4 _≡'_
-- data _≡'_ {a} {A : Set a} (x : A) : A → Set where
--   instance refl : x ≡' x

-- uip' :
--   {ℓ : Level}
--   {A : Set ℓ}
--   {x y : A}
--   (p q : x ≡' y)
--   → -----------
--   p ≡ q
-- uip' refl refl = refl

-- _≈'_ : {A : Set₁} → A → A → Ω 
-- prf (x ≈' y) = x ≡' y
-- equ (_ ≈' _) = uip'


-- ∥_∥' : ∀{a} → Set a → Ω
-- prf ∥ A ∥'     = (P : Ω) → (A → prf P) → prf P
-- equ ∥ A ∥' f g = funext (λ P → funext (λ h → equ P (f P h) (g P h)))

data Unit₁ : Set₁ where
  tt : Unit₁

postulate
  -- The universe
  U : Set₁
  u : Fib {Γ = Unit₁} (λ _ → U)
  El : Fib₀ U
  
  -- code :
  --   {Γ : Set₁}
  --   (A : Fib₀ Γ)
  --   → ----------
  --   Γ → U
  -- code-el :
  --   {Γ : Set₁}
  --   (A : Fib₀ Γ)
  --   → -----------------------
  --   Fib' (code A) El  ≡ A
  -- code :
  --   {Γ : Set₁}
  --   (A : Fib₀ Γ)
  --   → --------------
  --   ∥ Σ code ∈ (Γ → U) , Fib' code El ≡ A ∥'

ua : {Γ : Set₁}{A B : U} → A ~ B
ua {Γ} {A} {B} = {!!} , {!!} where
  p : Int → U
  p i = fst (u O' (λ _ → tt) ((i ≈O) ∨ (i ≈I)) q (A , {!!})) where
    q : [ (i ≈O) ∨ (i ≈I) ] → Int → U
    q u j = ∥∥-elim {!!} {!!} u

-- FibFibers : {Γ : Set₁}(A : Γ → Set) → Set₁
-- FibFibers {Γ} A = ((x : Γ) → Fib {Γ = Unit₁} (λ _ → A x))

-- FamFib→FibFam :
--   {Γ : Set₁}
--   (A : Γ → Set)
--   → ---------------
--   FibFibers A → Fib A
-- FamFib→FibFam {Γ} A fib-fibers = subst Fib eqFam α where
--   A' : Γ → U
--   A' x = code ((λ _ → A x) , fib-fibers x) tt
--   A'' : Γ → Set
--   A'' = fst (Fib' A' El)
--   α : Fib A''
--   α = snd (Fib' A' El)
--   eqFam : A'' ≡ A
--   eqFam = funext (λ x → cong (λ fib → fst fib tt) (code-el ((λ _ → A x) , fib-fibers x)))

El' : {Γ : Set₁} → (Γ → U) → Fib₀ Γ
El' f = Fib' f El

postulate
  pi    : {Γ : Set₁ } (A : Γ → U) (B : Σ Γ (fst (El' A)) → U) → U
  sigma : {Γ : Set₁ } (A : Γ → U) (B : Σ Γ (fst (El' A)) → U) → U
  path  : {Γ : Set₁ } (A : Γ → U) (B : Σ Γ (fst (El' A)) → U) → U
