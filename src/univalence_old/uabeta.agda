----------------------------------------------------------------------
-- This Agda code is designed to accompany the paper "Axioms for
-- Modelling Cubical Type Theory in a Topos". It is currently a work
-- in progress and still includes postulates/holes in certain places.
-- It also needs some tidying up and possibily reorganisation.
--
-- The idea for getting an impredicative universe of propositions Ω
-- comes from Martin Escardo, more details can be found at:
--
--          http://www.cs.bham.ac.uk/~mhe/impredicativity/          
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module univalence.uabeta where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.functions
open import Data.paths
open import equivs
open import univalence.core

coerce : {Γ : Set}{A B : Fib Γ} → IdU A B → (x : Γ) → fst A x → fst B x
coerce P = fst (idToEquiv P)

abstract
 helper : {Γ : Set}(A : Fib Γ)(x : Γ)(a : fst A x)
  → a ~ trivComp A I' x (trivComp A O' x a)
 helper (A , α) x a = (λ i → fst (p i)) , pO=a , pI=rhs where
  filler = fill O' α (λ _ → x) cofFalse ∅-elim a (λ ())
  cases : {i : Int} → (i ≡ O) ⊎ (i ≡ I) → Π (A ∘ (λ _ → x))
  cases (inl _) _ = a
  cases (inr refl) = fst (fill I' α (λ _ → x) cofFalse ∅-elim (fst filler I) (λ ()))
  left : {i : Int}{l : i ≡ O} → snd (((i ≈O) ∨ (i ≈I) , OI-elim cases) ∙ O) ∣ inl l ∣ ≡ fst filler i
  left {l = refl} = symm (snd (snd filler))
  right : {i : Int}{r : i ≡ I} → OI-elim cases ∣ inr r ∣ I ≡ fst filler i
  right {r = refl} = snd (snd (fill I' α (λ _ → x) cofFalse ∅-elim (fst filler I) (λ ())))
  p = λ i →  α I' (λ _ → x) ((i ≈O) ∨ (i ≈I)) (OI-elim cases)
    (fst filler i , or-elim-eq (λ u → OI-elim cases u I) (fst filler i)
    (λ {l} → left {l = l}) (λ {r} → right {r = r}))
  pO=a : fst (p O) ≡ a
  pO=a = symm (snd (p O) ∣ inl refl ∣)
  pI=rhs : fst (p I) ≡ trivComp (A , α) I' x (trivComp (A , α) O' x a)
  pI=rhs =
    proof:
        fst (p I)
      ≡[ symm (snd (p I) ∣ inr refl ∣) ]≡
        fst (fill I' α (λ _ → x) cofFalse ∅-elim (fst filler I) (λ ())) O
      ≡[ fillAtEnd I' α (λ _ → x) cofFalse ∅-elim (fst filler I) (λ ()) ]≡
        trivComp (A , α) I' x (fst filler I)
      ≡[ cong (trivComp (A , α) I' x) (fillAtEnd O' α (λ _ → x) cofFalse ∅-elim a (λ ())) ]≡
        trivComp (A , α) I' x (trivComp (A , α) O' x a)
    qed

uaβ' : {Γ : Set}(A B : Fib Γ)
  (f : (x : Γ) → fst A x → fst B x)
  (e : Equiv f)
  (P : IdU A B)
  → ----------------
  compOIProperty {Γ} {A} {B} f P → f ~ coerce P
uaβ' {Γ} _ _ f e ((P , ρ) , refl , refl) h =
  funextPath (λ x → funextPath (λ a →
    subst (λ b → f x a ~ b) (symm (h x a)) (helper (reindex' (P , ρ) (λ x → x , I)) x (f x a))))

uaβ : {Γ : Set}(A B : Fib Γ)
  (f : (x : Γ) → fst A x → fst B x)
  (e : Equiv f)
  → ----------------
  f ~ coerce (equivToId {Γ} {A} {B} f e)
uaβ {Γ} A B f e = uaβ' A B f e (equivToId {Γ} {A} {B} f e) (uaβhelper4 {Γ} {A} {B} f e)
