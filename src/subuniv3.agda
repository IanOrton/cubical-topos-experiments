open import Agda.Primitive public
open import Data.Product public
open import Function public
open import Relation.Binary.PropositionalEquality

data Unit₁ : Set₁ where
  tt : Unit₁

-- Let P be the property that A is constant
P  :
  {Γ : Set₁}
  → --------------
  (Γ → Set) → Set₁
P {Γ} A = (x y : Γ) → A x ≡ A y

-- Show that P is functorial 
P' :
  {Δ Γ : Set₁}
  {A : Γ → Set}
  (f : Δ → Γ)
  → --------------
  P A → P (A ∘ f)
P' f p x y = p (f x) (f y)

-- Then define the family of families with the P property
PFam : Set₁ → Set₁
PFam Γ = Σ[ A ∈ (Γ → Set) ] P A

PΠ : 
  {Γ : Set₁}
  (A : Γ → Set)
  (pA : P A)
  (B : Σ Γ A → Set)
  (pB : P B)
  → --------------
  P (λ x → (a : A x) → B (x , a))
PΠ A pA B pB x y = {!!} where
  Πext : (

  B' : A x → Set
  B' a = B (x , a)

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
  code : {Γ : Set₁}(A : PFam Γ) → Γ → U
  code-el : {Γ : Set₁}(A : PFam Γ) → PFam' (code A) El ≡ A

  funext : Extensionality (lsuc lzero) (lsuc lzero)

-- Say a family has P-fibres if all its fibres, viewed as
-- families over Unit, have the P property
PFib :
  {Γ : Set₁}
  → --------------
  (Γ → Set) → Set₁
PFib {Γ} A = (x : Γ) → P {Γ = Unit₁} (λ _ → A x)

-- Assuming extensionality at level 1 then if a
-- family has P-fibres then it is a P-family
PFib→PFam :
  {Γ : Set₁}
  (A : Γ → Set)
  → --------------
  PFib A → P A
PFib→PFam {Γ} A pFib = subst P proj₁APFam=A (proj₂ APFam) where
  AU : Γ → U
  AU x = code ((λ _ → A x) , pFib x) tt
  APFam : PFam Γ
  APFam = PFam' AU El
  proj₁APFam=A : proj₁ APFam ≡ A
  proj₁APFam=A = funext (λ x → cong (λ pfam → proj₁ pfam tt) (code-el ((λ _ → A x) , pFib x)))

-- Therefore all families are constant
AllConstant  :
  {Γ : Set₁}
  (A : Γ → Set)
  → --------------
  P A
AllConstant A = PFib→PFam A pFib where
  pFib : PFib A
  pFib x tt tt = refl
