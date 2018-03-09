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

module Data.functions where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.products
open import Data.paths

----------------------------------------------------------------------
-- Dependent functions
----------------------------------------------------------------------
Π' : {Γ : Set}(A : Γ → Set)(B : (Σ x ∈ Γ , A x) → Set) → Γ → Set
Π' A B x = (a : A x) → B (x , a)

FibΠid :
  {A : Int → Set}
  {B : (Σ x ∈ Int , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Π' A B)
FibΠid {A} {B} α β e p φ f g = (g₁ , extends) where
  pₐ : (a : A (p ⟨ ! e ⟩)) → Π (A ∘ p)
  pₐ a = fst (fill {A = A} (! e) α p cofFalse ∅-elim a (λ u → ∅-elim u))
  pₐI≡a : (a : A (p ⟨ ! e ⟩)) → pₐ a ⟨ ! e ⟩ ≡ a
  pₐI≡a a = snd (snd (fill {A = A} (! e) α p cofFalse ∅-elim a (λ u → ∅-elim u)))
  q : (a : A (p ⟨ ! e ⟩)) → Int → Σ Int A
  q a i = (p i , pₐ a i)
  f' : (a : A (p ⟨ ! e ⟩)) → [ φ ] → Π (B ∘ (q a))
  f' a u i = f u i (pₐ a i)
  b₀ : (a : A (p ⟨ ! e ⟩)) → ⟦ b ∈ (B (q a ⟨ e ⟩)) ∣ (φ , f' a) ∙ ⟨ e ⟩ ↗ b ⟧
  b₀ a = (fst g (pₐ a ⟨ e ⟩) , (λ u → cong (λ f → f (pₐ a ⟨ e ⟩)) (snd g u)))
  abstract
    g₁ : (Π' A B) (p ⟨ ! e ⟩)
    g₁ a = let b = fst (β e (q a) φ (f' a) (b₀ a)) in subst (λ a → B (p ⟨ ! e ⟩ , a)) (pₐI≡a a) b where
  abstract
   extends : prf ((φ , f) ∙ ⟨ ! e ⟩ ↗ g₁)
   extends u = funext (λ a → substLemma (pₐI≡a a) (trans (f'I≡g₁ a) (fI≡f'I a))) where
    substLemma : {a a' : A (p ⟨ ! e ⟩)}(eq : a' ≡ a){b : B (p ⟨ ! e ⟩ , a)}{b' : B (p ⟨ ! e ⟩ , a')}
      → subst (λ a → B (p ⟨ ! e ⟩ , a)) (symm eq) b ≡ b' → b ≡ subst (λ a → B (p ⟨ ! e ⟩ , a)) eq b'
    substLemma refl refl = refl
    f'I≡g₁ : (a : A (p ⟨ ! e ⟩)) → f' a u ⟨ ! e ⟩ ≡ fst (β e (q a) φ (f' a) (b₀ a))
    f'I≡g₁ a = snd (β e (q a) φ (f' a) (b₀ a)) u
    fI≡f'I : (a : A (p ⟨ ! e ⟩)) → subst (λ a₁ → B (p ⟨ ! e ⟩ , a₁)) (symm (pₐI≡a a)) (snd ((φ , f) ∙ ⟨ ! e ⟩) u a) ≡ f' a u ⟨ ! e ⟩
    fI≡f'I a = congdep (λ a' → f u ⟨ ! e ⟩ a') (symm (pₐI≡a a))

FibΠ :
  {Γ : Set}
  {A : Γ → Set}
  {B : (Σ x ∈ Γ , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Π' A B)
FibΠ {Γ} {A} {B} α β e p = FibΠid (reindex A α p) (reindex B β (p ×id)) e id

FibΠ' :
  {Γ : Set}
  (A : Fib Γ)
  (B : Fib (Σ x ∈ Γ , fst A x))
  → -----------
  Fib Γ
FibΠ' (A , α) (B , β) = (Π' A B , FibΠ {A = A} {B = B} α β)

Πext : {Γ : Set}{A : Γ → Set}{B : (Σ x ∈ Γ , A x) → Set}{x : Γ}{f g : Π' A B x} → ((a : A x) → f a ~ g a) → f ~ g
fst (Πext pointwise) i a = fst (pointwise a) i
fst (snd (Πext pointwise)) = funext (λ a → fst (snd (pointwise a)))
snd (snd (Πext pointwise)) = funext (λ a → snd (snd (pointwise a)))
  
----------------------------------------------------------------------
-- Forming Π-types is stable under reindexing
----------------------------------------------------------------------
reindexΠ :
  {Δ Γ : Set}
  (A : Γ → Set)
  (B : Σ Γ A → Set)
  (α : isFib A)
  (β : isFib B)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Π' A B) (FibΠ {B = B} α β) ρ ≡ FibΠ {B = B ∘ (ρ ×id)} (reindex A α ρ) (reindex B β (ρ ×id))
reindexΠ A B α β ρ = refl
