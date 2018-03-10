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
module hcomp-trans where

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
-- Transport structure (CHM)
----------------------------------------------------------------------
Transport : ∀{ℓ}{Γ : Set ℓ} (e : OI) (A : Γ → Set) (p : Int → Γ) → Set ℓ
Transport e A p = (φ : Cof) (cst : [ φ ] → (i : Int) → p ⟨ e ⟩ ≡ p i) →
  (x₁ : A (p ⟨ e ⟩)) →
  ⟦ x₀ ∈ (A (p ⟨ ! e ⟩)) ∣ (φ , (λ u → subst A (cst u ⟨ ! e ⟩) x₁)) ↗ x₀ ⟧

isTranspFib : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → Set ℓ
isTranspFib {Γ = Γ} A = (e : OI) (p : Int → Γ) → Transport e A p

TranspFib : ∀{ℓ}(Γ : Set ℓ) → Set (lsuc lzero ⊔ ℓ)
TranspFib {a} Γ = Σ (Γ → Set) isTranspFib

----------------------------------------------------------------------
-- Reindexing transport structures (CHM)
----------------------------------------------------------------------

transpReindex : ∀{ℓ}{Δ Γ : Set ℓ}(A : Γ → Set)(α : isTranspFib A)(ρ : Δ → Γ) → isTranspFib (A ∘ ρ)
transpReindex A α ρ e p φ cst x₁ =
  subst
    (λ f → ⟦ x₀ ∈ ((A ∘ ρ) (p ⟨ ! e ⟩)) ∣ (φ , f) ↗ x₀ ⟧)
    (funext (λ u → symm (substcong A ρ (cst u ⟨ ! e ⟩) x₁)))
    (α e (ρ ∘ p) φ (λ u i → cong ρ (cst u i)) x₁)

transpReindex' : ∀{ℓ}{Δ Γ : Set ℓ}(Aα : TranspFib Γ)(ρ : Δ → Γ) → TranspFib Δ
transpReindex' (A , α) ρ = (A ∘ ρ , transpReindex A α ρ)

----------------------------------------------------------------------
-- A map which is a homogeneous and transport fibration is a fibration (CHM)
----------------------------------------------------------------------

fibToHomog : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → isFib A → isHomogFib A
fibToHomog A α e x = α e (λ _ → x)

fibToTransp : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → isFib A → isTranspFib A
fibToTransp A α e p φ cst x₁ = α e p φ (λ u i → subst A (cst u i) x₁) (x₁ , extends)
  where
  extends : (u : [ φ ]) → subst A (cst u ⟨ e ⟩) x₁ ≡ x₁
  extends u = cong (λ eq → subst A eq x₁) (uip (cst u ⟨ e ⟩) refl)

homogAndTranspToFib : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → isHomogFib A → isTranspFib A → isFib A
homogAndTranspToFib {Γ = Γ} A hα tα e p φ f (x₁ , extends₁) =
  subst (λ g → ⟦ x₀ ∈ ((A ∘ p) ⟨ ! e ⟩) ∣ (φ , g) ↗ x₀ ⟧)
    (funext (λ u → symm (snd (f' u ⟨ ! e ⟩) refl)))
    (hα e (p ⟨ ! e ⟩) φ (λ u i → fst (f' u i)) (x₁' , extends₁'))
  where
  p' : Int → Int → Γ
  p' i j = p (cnx (! e) i j)

  -- arguments transported into !e

  fcst : (u : [ φ ]) → (i : Int) → [ i ≈OI ! e ] → (j : Int) → p' i ⟨ e ⟩ ≡ p' i j
  fcst u i v j = subst (λ k → p' k ⟨ e ⟩ ≡ p' k j) (symm v) refl

  f' : (u : [ φ ]) → (i : Int) →
    ⟦ f' ∈ (A ∘ p) ⟨ ! e ⟩ ∣ (i ≈OI ! e , λ v → subst A (fcst u i v ⟨ ! e ⟩) (f u i)) ↗ f' ⟧
  f' u i = tα e (p' i) (i ≈OI ! e) (fcst u i) (f u i)

  x₁' : (A ∘ p) ⟨ ! e ⟩
  x₁' = fst (tα e p cofFalse ∅-elim x₁)

  extends₁' : (u : [ φ ]) → fst (f' u ⟨ e ⟩) ≡ x₁'
  extends₁' u =
    cong (λ {(y₁ , ψ , cst) → fst (tα e p ψ cst y₁)})
      (×ext (extends₁ u)
        (Σext (cofEq (propext e≠!e ∅-elim)) (funext (λ v → ∅-elim v))))

----------------------------------------------------------------------
-- Transport fibrations are closed under post-composition with any endofunctor
-- (Actually, we don't even need the "functor" to preserve composition)
----------------------------------------------------------------------

record DemiEndo : Set (lsuc lzero) where
  field
    obf : Set → Set
    homf : {A B : Set} → (A → B) → (obf A → obf B)
    presid : (A : Set) → homf (λ (a : A) → a) ≡ (λ a → a)

open DemiEndo public

endosubst : ∀ {ℓ}{Γ : Set ℓ} (F : DemiEndo) (A : Γ → Set) {x y : Γ} (p : x ≡ y)
  → homf F (subst A p) ≡ subst (obf F ∘ A) p
endosubst F A refl = presid F (A _)

TranspFibEndo : ∀{ℓ} {Γ : Set ℓ} (F : DemiEndo) (A : Γ → Set) → isTranspFib A → isTranspFib (obf F ∘ A)
TranspFibEndo F A tα e p φ cst y₁ =
  transpMap y₁ , λ u → cong (λ g → g y₁) (extendsMap u)
  where
  transpMap : (obf F ∘ A ∘ p) ⟨ e ⟩ → (obf F ∘ A ∘ p) ⟨ ! e ⟩
  transpMap = homf F (λ x₁ → fst (tα e p φ cst x₁))

  extendsMap : prf ((φ , λ u → subst (obf F ∘ A) (cst u ⟨ ! e ⟩)) ↗ transpMap)
  extendsMap u =
    trans
      (cong (homf F) (funext (λ x₁ → snd (tα e p φ cst x₁) u)))
      (symm (endosubst F A (cst u ⟨ ! e ⟩)))
