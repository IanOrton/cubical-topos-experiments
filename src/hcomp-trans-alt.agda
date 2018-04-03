----------------------------------------------------------------------
-- This Agda code is designed to accompany the paper "Axioms for
-- Modelling Cubical Type Theory in a Topos" (CSL Special Issue
-- version). 
--
-- The idea for getting an impredicative universe of propositions Ω
-- comes from Martin Escardo, more details can be found at:
--
--          http://www.cs.bham.ac.uk/~mhe/impredicativity/          
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module hcomp-trans-alt where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import replace -- only using substcong

----------------------------------------------------------------------
-- Decomposition of the composition operation into homogeneous
-- composition and transport operations. Most of these definitions are
-- taken from Coquand-Huber-Mörtberg,
-- "On Higher Inductive Types in Cubical Type Theory"
----------------------------------------------------------------------

----------------------------------------------------------------------
-- Homogeneous path composition structure (CHM)
----------------------------------------------------------------------
HomogComp : OI → Set → Set
HomogComp e A = (φ : Cof)(f : [ φ ] → (Int → A)) →
  ⟦ x₁ ∈ A ∣ (φ , f) ∙ ⟨ e ⟩ ↗ x₁ ⟧ →
  ⟦ x₀ ∈ A ∣ (φ , f) ∙ ⟨ ! e ⟩ ↗ x₀ ⟧

isHomogFib : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → Set ℓ
isHomogFib {Γ = Γ} A = (e : OI)(x : Γ) → HomogComp e (A x)

HomogFib : ∀{ℓ}(Γ : Set ℓ) → Set (lsuc lzero ⊔ ℓ)
HomogFib {ℓ} Γ = Σ (Γ → Set) isHomogFib

fiberwiseFibrantIsHomogFib : ∀ {ℓ}{Γ : Set ℓ} (A : Γ → Set) →
  (∀ x → isFibObj (A x)) → isHomogFib A
fiberwiseFibrantIsHomogFib A fα e x = fα x e (λ _ → tt)


----------------------------------------------------------------------
-- Transport structure (CHM, old definition)
----------------------------------------------------------------------
Transport : ∀{ℓ}{Γ : Set ℓ} (e : OI) (A : Γ → Set) (p : Int → Γ) → Set ℓ
Transport e A p = (φ : Cof) (cst : [ φ ] → (i : Int) → p ⟨ e ⟩ ≡ p i) →
  (x₁ : A (p ⟨ e ⟩)) →
  ⟦ x₀ ∈ (A (p ⟨ ! e ⟩)) ∣ (φ , (λ u → subst A (cst u ⟨ ! e ⟩) x₁)) ↗ x₀ ⟧

isTranspFib : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → Set ℓ
isTranspFib {Γ = Γ} A = (e : OI) (p : Int → Γ) → Transport e A p


----------------------------------------------------------------------
-- Transport structure (CHM, alternative definition)
----------------------------------------------------------------------
Transport' : ∀{ℓ}{Γ : Set ℓ} (e : OI) (A : Int → Set) → Set₁
Transport' e A = (φ : Cof) (cst : [ φ ] → (i : Int) → A ⟨ e ⟩ ≡ A i) →
  (x₁ : A ⟨ e ⟩) →
  ⟦ x₀ ∈ (A ⟨ ! e ⟩) ∣ (φ , (λ u → coe (cst u ⟨ ! e ⟩) x₁)) ↗ x₀ ⟧

isTranspFib' : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → Set (lsuc lzero ⊔ ℓ)
isTranspFib' {Γ = Γ} A = (e : OI) (p : Int → Γ) → Transport' {Γ = Γ} e (A ∘ p)

-- Not sure if this is true:
--   old→new : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → isTranspFib A → isTranspFib' A
--   old→new A tα e p φ cst x₁ = tα e p φ {!!} x₁

new→old : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → isTranspFib' A → isTranspFib A
new→old A tα e p φ cst x₁ = (fst x₀,ext , λ u → trans (snd x₀,ext u) (subst-coe-cong (cst u ⟨ ! e ⟩))) where
  x₀,ext : ⟦ x₀ ∈ (A (p ⟨ ! e ⟩)) ∣ (φ , (λ u → coe (cong A (cst u ⟨ ! e ⟩)) x₁)) ↗ x₀ ⟧
  x₀,ext = tα e p φ (λ u i → cong A (cst u i)) x₁
  subst-coe-cong : ∀{ℓ}{A : Set ℓ}{B : A → Set}{x y : A}(p : x ≡ y){b : B x} → subst B p b ≡ coe (cong B p) b
  subst-coe-cong refl = refl


----------------------------------------------------------------------
-- The new definition still allows us to prove the following:
----------------------------------------------------------------------
fibToTransp : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → isFib A → isTranspFib' A
fibToTransp A α e p φ cst x₁ = α e p φ (λ u i → coe (cst u i) x₁) (x₁ , extends)
  where
  extends : (u : [ φ ]) → coe (cst u ⟨ e ⟩) x₁ ≡ x₁
  extends u = cong (λ eq → coe eq x₁) (uip (cst u ⟨ e ⟩) refl)

homogAndTranspToFib' : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → isHomogFib A → isTranspFib' A → isFib A
homogAndTranspToFib' {Γ = Γ} A hα tα e p φ f (x₁ , extends₁) =
  subst (λ g → ⟦ x₀ ∈ ((A ∘ p) ⟨ ! e ⟩) ∣ (φ , g) ↗ x₀ ⟧)
    (funext (λ u → symm (snd (f' u ⟨ ! e ⟩) refl)))
    (hα e (p ⟨ ! e ⟩) φ (λ u i → fst (f' u i)) (x₁' , extends₁'))
  where
  p' : Int → Int → Γ
  p' i j = p (cnx (! e) i j)

  -- arguments transported into !e

  fcst : (u : [ φ ]) → (i : Int) → [ i ≈OI ! e ] → (j : Int) → A (p' i ⟨ e ⟩) ≡ A (p' i j)
  fcst u i v j = cong A (subst (λ k → p' k ⟨ e ⟩ ≡ p' k j) (symm v) refl)

  f' : (u : [ φ ]) → (i : Int) →
    ⟦ f' ∈ (A ∘ p) ⟨ ! e ⟩ ∣ (i ≈OI ! e , λ v → coe (fcst u i v ⟨ ! e ⟩) (f u i)) ↗ f' ⟧
  f' u i = tα e (p' i) (i ≈OI ! e) (fcst u i) (f u i)

  x₁' : (A ∘ p) ⟨ ! e ⟩
  x₁' = fst (tα e p cofFalse ∅-elim x₁)

  extends₁' : (u : [ φ ]) → fst (f' u ⟨ e ⟩) ≡ x₁'
  extends₁' u =
    cong (λ {(y₁ , ψ , cst) → fst (tα e p ψ cst y₁)})
      (×ext (extends₁ u)
        (Σext (cofEq (propext e≠!e ∅-elim)) (funext (λ v → ∅-elim v))))
