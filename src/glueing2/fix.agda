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
module glueing2.fix where 

open import glueing2.core
open import glueing2.strict
open import glueing2.fixcore

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

postulate
 FibSGlueid :
  {Φ : Int → Cof}
  {A : res Int Φ → Set}
  {B : Int → Set}
  (f : (x : Int)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Int)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  isFib A → isFib B → isFib (λ i → SGlue (Φ i) (λ u → A (i , u)) (B i) (f i))
 -- FibSGlue {Γ} {Φ} {A} {B} f equiv α β =
 --  FibFix {Φ = Φ} {G = SGlue Φ A B f} (subst isFib A≡Gfst α) (FibSGlue' f equiv α β) where
 --    A≡Gfst : A ≡ (SGlue Φ A B f) ∘ fst
 --    A≡Gfst = symm (funext (λ{ (x , u) → strictness Φ A B f x u}))


FibSGlue :
  {Γ : Set}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  isFib A → isFib B → isFib (λ i → SGlue (Φ i) (λ u → A (i , u)) (B i) (f i))
FibSGlue {Γ} {Φ} {A} {B} f equiv α β e p = FibSGlueid (λ x → f (p x)) (λ x → equiv (p x)) (reindex A α (λ{ (i , u) → (p i , u)})) (reindex B β p) e id


SGlueFib :
  {Γ : Set}
  (Φ : Γ → Cof)
  (A : Fib (res Γ Φ))
  (B : Fib Γ)
  (f : (x : Γ)(u : [ Φ x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → --------------
  Fib Γ
SGlueFib {Γ} Φ (A , α) (B , β) f equiv = (λ i → SGlue (Φ i) (λ u → A (i , u)) (B i) (f i)) , FibSGlue {Γ} {Φ} {A} {B} f equiv α β

postulate
 SGlueReindex :
  {Γ : Set}
  (Φ : Γ → Cof)
  (A : Fib (res Γ Φ))
  (B : Fib Γ)
  (f : (x : Γ)(u : [ Φ x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → --------------
  reindex' (SGlueFib Φ A B f equiv) fst ≡ A

SGlueReindex' :
  {Γ : Set}
  (Φ : Γ → Cof)
  (A : Fib (res Γ Φ))
  (B : Fib Γ)
  (f : (x : Γ)(u : [ Φ x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  (u : (x : Γ) → [ Φ x ]) 
  → --------------
  SGlueFib Φ A B f equiv ≡ reindex' A (λ x → x , u x)
abstract
  SGlueReindex' Φ A B f equiv u = cong (λ A → reindex' A (λ x → x , u x)) (SGlueReindex Φ A B f equiv)

--  SGlueReindex {Γ} Φ (A , α) (B , β) f equiv =
--    Σext (funext (λ{ (x , u) → strictness Φ A B f x u }))
--      (trans (substsubst {p = symm Gfst≡A} {q = Gfst≡A} α)
--        (cong (subst isFib Gfst≡A)
--          (isFixed {Φ = Φ} {G = SGlue Φ A B f}
--            (subst isFib (symm Gfst≡A) α) (FibSGlue' {Γ} {Φ} {A} {B} f equiv α β))))
--    where
--      Gfst≡A : (SGlue Φ A B f) ∘ fst ≡ A
--      Gfst≡A = funext (λ{ (x , u) → strictness Φ A B f x u})
--      substsubst : {x y : (res Γ Φ) → Set}{p : x ≡ y}{q : y ≡ x}(z : isFib x) → subst isFib q (subst isFib p z) ≡ z
--      substsubst {p = refl} {q = refl} _ = refl

--  uaβhelper :
--   {Γ : Set}
--   (A : Fib (res (Γ × Int) i=OI))
--   (B : Fib (Γ × Int))
--   (f : (x : Γ × Int)(u : [ i=OI x ]) → fst A (x , u) → fst B x)
--   (equiv : (x : Γ × Int)(v : [ i=OI x ]) → Equiv' (f x v))
--   (x : Γ)
--   → --------------
--   FibSGlue {Φ = i=OI} f equiv (snd A) (snd B) O' < x ,id>
--     ≡ FibSGlue' f equiv (snd A) (snd B) O' < x ,id>
--  uaβhelper (A , α) (B , β) f equiv x =
--   sameOtherwise {G = SGlue i=OI A B f} (subst isFib A≡Gfst α) (FibSGlue' f equiv α β) O' < x ,id> ¬∀i=OI where
--     A≡Gfst : A ≡ (SGlue i=OI A B f) ∘ fst
--     A≡Gfst = symm (funext (λ{ (x , u) → strictness i=OI A B f x u}))
--     ¬∀i=OI : [ ∀i (λ i → (i ≈O) ∨ (i ≈I)) ] → ∅
--     ¬∀i=OI ∀i=OI = O≠I (subst prf O≈O≡O≈I refl) where
--         cases : {i : Int} → (i ≡ O) ⊎ (i ≡ I) → prf ((O ≈ i) or ¬ (O ≈ i))
--         cases (inl i=O) = ∣ inl (symm i=O) ∣
--         cases (inr i=I) = ∣ inr (λ O=i → ∅-elim (O≠I (trans i=I O=i))) ∣
--         O≈O≡O≈I : (O ≈ O) ≡ (O ≈ I)
--         O≈O≡O≈I = cntd' (λ i → O ≈ i) (λ i → ∥∥-elim cases (λ _ _ → eq ((O ≈ i) or ¬ (O ≈ i))) (∀i=OI i)) O
