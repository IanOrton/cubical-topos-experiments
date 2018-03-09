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
  -- P' :
  --   {Δ Γ : Set₁}
  --   {A : Γ → Set}
  --   (f : Δ → Γ)
  --   → --------------
  --   P A → P (A ∘ f)

-- Then define the family of families with the P property
PFam : Set₁ → Set₁
PFam Γ = Σ A ∈ (Γ → Set) , P A

-- This is also functorial
-- PFam' :
--   {Δ Γ : Set₁}
--   (f : Δ → Γ)
--   → --------------
--   PFam Γ → PFam Δ
-- PFam' f (A , p) = (A ∘ f , P' f p)
  
-- Postulate a generic universe of P-families
postulate
  U  : Set₁
  El : U → Set
  decode : {Γ : Set₁} → (A : Γ → U)  → P (El ∘ A)
  code   : {Γ : Set₁} → (A : PFam Γ) → Γ → U
  code-decode :
    {Γ : Set₁} → (A : Γ → U) → code (El ∘ A , (decode A)) ≡ A
  decode-code :
    {Γ : Set₁} → (A : PFam Γ) → (El ∘ code A , decode (code A)) ≡ A

PEl : P El
PEl = decode (λ A → A)

-- Say a family has P-fibres if all its fibres, viewed as
-- families over Unit, have the P property
PFib :
  {Γ : Set₁}
  → --------------
  (Γ → Set) → Set₁
PFib {Γ} A = (x : Γ) → P {Γ = Unit₁} (λ _ → A x)


PFib→PFam :
  {Γ : Set₁}
  (A : Γ → Set)
  → --------------
  PFib A → P A
PFib→PFam {Γ} A pFib = subst P El∘AU≡A (decode AU) where
  AU : Γ → U 
  AU x = code ((λ _ → A x) , (pFib x)) tt
  El∘AU≡A : El ∘ AU ≡ A
  El∘AU≡A = funext (λ x → let rr = cong (λ pfam → fst pfam tt) (decode-code ((λ _ → A x) , (pFib x))) in rr)
--  APFam : prf ∥ PFam Γ ∥
--  APFam = ∥∥-rec ∥ PFam Γ ∥ (λ A → ∣ El* A ∣) AUex --PFam' AU El
--  proj₁APFam=A : fst APFam ≡ A
--  proj₁APFam=A = {!!} -- funext (λ x → cong (λ pfam → proj₁ pfam tt) (code-el ((λ _ → A x) , pFib x)))
