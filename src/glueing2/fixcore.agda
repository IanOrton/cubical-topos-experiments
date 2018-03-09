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
module glueing2.fixcore where 

open import glueing2.core
open import glueing2.strict

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import equivs
open import Data.paths
open import Data.products

----------------------------------------------------------------------
-- Fixing the composition
----------------------------------------------------------------------

-- ∀i : (p : Int → Cof) → Cof
-- fst (∀i p) = All i ∈ Int , fst (p i)
-- snd (∀i p) = cof∀ (fst ∘ p) (λ i → snd (p i))

-- abstract
--  FibFix :
--   {Γ : Set}
--   {Φ : Γ → Cof}
--   {G : Γ → Set}
--   → ---------------
--   (α : isFib {Γ = res Γ Φ} (G ∘ fst)) → isFib G → isFib G
--  FibFix {Γ} {Φ} {G} α γ e p ψ f (g , ext) = let g' = γ e p (ψ ∨ ∀i (Φ ∘ p)) f' (g , ext') in (fst g') , (λ u → snd g' ∣ inl u ∣) where
--   aFill : (∀iΦ : [ ∀i (Φ ∘ p) ]) →
--     ⟦ a' ∈ ((i : Int) → G (p i)) ∣
--       ((ψ , f) ↗ a') & (a' ⟨ e ⟩ ≈ g) ⟧
--   aFill ∀iΦ = fill {A = G ∘ fst} e α (λ i → (p i) , ∀iΦ i) ψ f g ext
--   f' : [ ψ ∨ ∀i (Φ ∘ p) ] → Π (G ∘ p)
--   f' = _∪_ {φ = ψ} {ψ = ∀i (Φ ∘ p)} f (λ u → fst (aFill u)) {λ v ∀Φi → fst (snd (aFill ∀Φi)) v}
--   ext' : prf ((ψ ∨ ∀i (Φ ∘ p) , f') ∙ ⟨ e ⟩ ↗ g)
--   ext' = or-elim-eq (λ u → f' u ⟨ e ⟩) g (λ {l} → ext l) (λ {r} → snd (snd (aFill r)))

--  isFixed : 
--   {Γ : Set}
--   {Φ : Γ → Cof}
--   {G : Γ → Set}
--   (α : isFib {Γ = res Γ Φ} (G ∘ fst))
--   (γ : isFib G)
--   → ---------------
--   reindex G (FibFix {Φ = Φ} {G} α γ) fst ≡ α
--  isFixed {Γ} {Φ} {G} α γ = fibExt {A = G ∘ fst} calc where
--   calc : (e : OI) (p : Int → Σ Γ (λ x → [ Φ x ])) (φ : Cof)
--       (f : [ φ ] → Π (G ∘ fst ∘ p))
--       (a₀ : set (G (fst (p ⟨ e ⟩))) (_↗_ ((φ , f) ∙ ⟨ e ⟩))) →
--       fst (reindex G (FibFix {Γ} {Φ} {G} α γ) fst e p φ f a₀) ≡ fst (α e p φ f a₀)
--   calc e p ψ f (g , ext) =
--     proof:
--       fst (FibFix {Γ} {Φ} {G} α γ e p' ψ f (g , ext))
--     ≡[ refl ]≡
--       fst (γ e p' (ψ ∨ ∀i (Φ ∘ p')) f' (g , ext'))
--     ≡[ symm (snd (γ e p' (ψ ∨ ∀i (Φ ∘ p')) f' (g , ext')) ∣ inr (λ i → snd (p i)) ∣) ]≡
--       fst (aFill (λ i → snd (p i))) ⟨ ! e ⟩
--     ≡[ fillAtEnd e α p ψ f g ext ]≡
--       fst (α e p ψ f (g , ext))
--     qed where
--       p' : Int → Γ
--       p' i = fst (p i)
--       aFill : (∀iΦ : [ ∀i (Φ ∘ p') ]) →
--         ⟦ a' ∈ ((i : Int) → G (p' i)) ∣
--           ((ψ , f) ↗ a') & (a' ⟨ e ⟩ ≈ g) ⟧
--       aFill ∀iΦ = fill {A = G ∘ fst} e α (λ i → (p' i) , ∀iΦ i) ψ f g ext
--       f' : [ ψ ∨ ∀i (Φ ∘ p') ] → Π (G ∘ p')
--       f' = _∪_ {φ = ψ} {ψ = ∀i (Φ ∘ p')} f (λ u → fst (aFill u)) {λ v ∀Φi → fst (snd (aFill ∀Φi)) v}
--       ext' : prf ((ψ ∨ ∀i (Φ ∘ p') , f') ∙ ⟨ e ⟩ ↗ g)
--       ext' = or-elim-eq (λ u → f' u ⟨ e ⟩) g (λ {l} → ext l) (λ {r} → snd (snd (aFill r)))

--  -- A tweaked extentionality principle for fibration structures
--  fibExt' : {Γ : Set}{A : Γ → Set}{α α' : isFib A}(e : OI)(p : Int → Γ)
--   → ((φ : Cof)(f : [ φ ] → Π (A ∘ p))
--      (a₀ : ⟦ x₁ ∈ (A (p ⟨ e ⟩)) ∣ (φ , f) ∙ ⟨ e ⟩ ↗ x₁ ⟧) → fst (α e p φ f a₀) ≡ fst (α' e p φ f a₀))
--   → α e p ≡ α' e p
--  fibExt' {α = α} {α'} e p ext =
--   funext (λ φ → funext (λ f → funext (λ a₀ →
--     incMono (λ x → (φ , f) ∙ ⟨ ! e ⟩ ↗ x) (α e p φ f a₀) (α' e p φ f a₀) (ext φ f a₀))))

--  sameOtherwise :
--   {Γ : Set}
--   {Φ : Γ → Cof}
--   {G : Γ → Set}
--   (α : isFib {Γ = res Γ Φ} (G ∘ fst))
--   (γ : isFib G)
--   (e : OI)
--   (p : Int → Γ)
--   (¬∀Φ : [ ∀i (Φ ∘ p) ] → ∅)
--   → ---------------
--   FibFix {Φ = Φ} {G} α γ e p ≡ γ e p
--  sameOtherwise {Γ} {Φ} {G} α γ e p ¬∀Φ =
--   fibExt' {A = G} {α = FibFix {Φ = Φ} {G} α γ} {α' = γ} e p calc where
--     calc : (φ : Cof) (f : [ φ ] → Π (G ∘ p))
--       (a₀ : set (G (p ⟨ e ⟩)) (_↗_ ((φ , f) ∙ ⟨ e ⟩))) →
--       fst (FibFix {Φ = Φ} {G} α γ e p φ f a₀) ≡ fst (γ e p φ f a₀)
--     calc ψ f (g , ext)  = 
--       proof:
--           fst (γ e p (ψ ∨ ∀i (Φ ∘ p)) f' (g , ext'))
--         ≡[ cong (λ ψfext → fst (γ e p (fst (fst ψfext)) (snd (fst ψfext)) (g , snd ψfext)) ) tripleEq ]≡
--           fst (γ e p ψ f (g , ext))
--       qed
--      where
--       aFill : (∀iΦ : [ ∀i (Φ ∘ p) ]) →
--         ⟦ a' ∈ ((i : Int) → G (p i)) ∣
--           ((ψ , f) ↗ a') & (a' ⟨ e ⟩ ≈ g) ⟧
--       aFill ∀iΦ = fill {A = G ∘ fst} e α (λ i → (p i) , ∀iΦ i) ψ f g ext
--       f' : [ ψ ∨ ∀i (Φ ∘ p) ] → Π (G ∘ p)
--       f' = _∪_ {φ = ψ} {ψ = ∀i (Φ ∘ p)} f (λ u → fst (aFill u)) {λ v ∀Φi → fst (snd (aFill ∀Φi)) v}
--       ext' : prf ((ψ ∨ ∀i (Φ ∘ p) , f') ∙ ⟨ e ⟩ ↗ g)
--       ext' = or-elim-eq (λ u → f' u ⟨ e ⟩) g (λ {l} → ext l) (λ {r} → snd (snd (aFill r)))
--       pairEq : _≡_ {A = Σ ψ ∈ Cof , ([ ψ ] → Π (G ∘ p))} (ψ ∨ ∀i (Φ ∘ p) , f') (ψ , f)
--       pairEq = lemma propsEq
--         (or-elim (λ u → f' u ≡ f (subst [_] propsEq u)) (λ u → uip)
--           (λ u → cong f (eq (fst ψ))) (λ u → ∅-elim (¬∀Φ u))) where
--           lemma : {X : Set}{ψ ψ' : Cof}{f : [ ψ ] → X}{f' : [ ψ' ] → X}
--             (p : ψ ≡ ψ') → ((u : [ ψ ]) → f u ≡ f' (subst [_] p u))
--             → _≡_ {A = Σ ψ ∈ Cof , ([ ψ ] → X)} (ψ , f) (ψ' , f')
--           lemma refl eq = Σext refl (funext eq)
--           propsEq : (ψ ∨ ∀i (Φ ∘ p)) ≡ ψ
--           propsEq = cofEq (propext
--             (λ u → u (fst ψ) (λ{ (inl x) → x ; (inr x) → ∅-elim (¬∀Φ x)}))
--             (λ u _ v → v (inl u)))
--       tripleEq : ((ψ ∨ ∀i (Φ ∘ p) , f') , ext') ≡ ((ψ , f) , ext)
--       tripleEq = Σext pairEq (eq ((ψ , f) ∙ ⟨ e ⟩ ↗ g))
