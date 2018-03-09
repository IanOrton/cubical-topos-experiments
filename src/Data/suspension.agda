{-# OPTIONS --rewriting #-}

module Data.suspension where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations

open import Data.paths

CompObj : OI → Set → Set
CompObj e A = (φ : Cof)(f : [ φ ] → Int → A) →
  ⟦ x₁ ∈ A ∣ (φ , f) ∙ ⟨ e ⟩ ↗ x₁ ⟧ →
  ⟦ x₀ ∈ A ∣ (φ , f) ∙ ⟨ ! e ⟩ ↗ x₀ ⟧

isFibObj : Set → Set
isFibObj A = (e : OI) → CompObj e A

-- This should follow from the fact that fibrations are closed under Σ
-- but needs boilerplate work since isFibObj !≡ isFib {Γ = Unit}. TODO.
postulate
  ΣFib' : {A : Set}{B : A → Set}(α : isFibObj A)(β : isFib B) → isFibObj (Σ A B)

lift : {A B : Set}(φ : Cof){f : [ φ ] → A}(α : A → B) → ⟦ x ∈ A ∣ (φ , f) ↗ x ⟧ → ⟦ y ∈ B ∣ (φ , λ u → α (f u)) ↗ y ⟧
lift _ α (x , ext) = (α x , λ u → cong α (ext u))

record Σ-alg (X : Set) : Set₁ where
 field
  obj : Set
  h   : isFibObj obj
  n   : obj
  s   : obj
  l   : (x : X) → n ~ s

open Σ-alg

record Σ-map {X : Set}(A B : Σ-alg X) : Set where
 field
  map    : obj A → obj B
  n-pres : map (n A) ≡ n B
  s-pres : map (s A) ≡ s B
  l-pres : (x : X)(i : Int) → map ((l A x) at i) ≡ (l B x) at i
  h-pres :
    (e : OI)
    (φ : Cof)
    (f : [ φ ] → Int → obj A)
    (x₀ : ⟦ x₁ ∈ obj A ∣ (φ , f) ∙ ⟨ e ⟩ ↗ x₁ ⟧)
    → -----------------------
    map (fst (h A e φ f x₀)) ≡ fst (h B e φ (λ u i → map (f u i)) (lift φ map x₀))

open Σ-map

idΣ : {X : Set}{A : Σ-alg X} → Σ-map A A
map idΣ = id
n-pres idΣ = refl
s-pres idΣ = refl
l-pres idΣ _ _ = refl
h-pres (idΣ {_} {A}) e φ f x = cong (λ x → fst (h A e φ f x)) (Σext refl (funext λ u → symm cong-id)) where
  cong-id : {A : Set}{x y : A}{p : x ≡ y} → cong id p ≡ p
  cong-id {p = refl} = refl

_∘Σ_ : {X : Set}{A B C : Σ-alg X}(g :  Σ-map B C)(f :  Σ-map A B) →  Σ-map A C
map (β ∘Σ α) = map β ∘ map α
n-pres (_∘Σ_ {C = C} β α) = subst (λ x → map β x ≡ n C) (symm (n-pres α)) (n-pres β)
s-pres (_∘Σ_ {C = C} β α) = subst (λ x → map β x ≡ s C) (symm (s-pres α)) (s-pres β)
l-pres (_∘Σ_ {C = C} β α) x i = subst (λ u → map β u ≡ l C x at i) (symm (l-pres α x i)) (l-pres β x i)
h-pres (_∘Σ_ {C = C} β α) e φ f x₀ =
  trans
    (cong (λ x → fst (h C e φ (λ u i → map β (map α (f u i))) x)) (Σext refl (funext λ _ → uipImp)))
    (trans
      (h-pres β e φ (λ u i → map α (f u i)) (lift φ (map α) x₀))
      (cong (map β) (h-pres α e φ f x₀))
    )

record Initial-Σ-alg (X : Set) : Set₁ where
 field
  Alg     : Σ-alg X
  initial : (B : Σ-alg X) → Σ-map Alg B
  unique  : {B : Σ-alg X}(α β : Σ-map Alg B) → α ≡ β

open Initial-Σ-alg

postulate
  initial-Σ-alg : (X : Set) → Initial-Σ-alg X

init-Σ-alg : (X : Set) → Σ-alg X
init-Σ-alg X = Alg (initial-Σ-alg X)

Susp : Set → Set
Susp X = obj (init-Σ-alg X)

north : {X : Set} → Susp X
north {X} = n (init-Σ-alg X)

south : {X : Set} → Susp X
south {X} = s (init-Σ-alg X)

merid : {X : Set}(x : X) → north ~ south
merid {X} = l (init-Σ-alg X)

open import Agda.Builtin.TrustMe

Σ-elim :
  (X  : Set)
  (P  : Susp X → Set)
  (ρ  : isFib P)
  (an : P north)
  (as : P south)
  (al : (x : X)(i : Int) → P (merid x at i))
  (lO : (x : X) → subst P (atO (merid x)) (al x O) ≡ an)
  (lI : (x : X) → subst P (atI (merid x)) (al x I) ≡ as)
  → ---------------------
  (x : Susp X) → P x
Σ-elim X P ρ an as al lO lI x = subst P π₁∘α=id (snd (map α x)) where

  ΣSuspP : Σ-alg X
  obj ΣSuspP = Σ x ∈ Susp X , P x
  h ΣSuspP = ΣFib' (h (init-Σ-alg X)) ρ
  n ΣSuspP = north , an
  s ΣSuspP = south , as
  fst (l ΣSuspP x) i = merid x at i , al x i
  fst (snd (l ΣSuspP x)) = Σext (atO (merid x)) (lO x)
  snd (snd (l ΣSuspP x)) = Σext (atI (merid x)) (lI x)

  π₁ : Σ-map ΣSuspP (init-Σ-alg X)
  map π₁ = fst
  n-pres π₁ = refl
  s-pres π₁ = refl
  l-pres π₁ x i = refl
  h-pres π₁ e φ f x₀ = primTrustMe  -- Should be provable once ΣFib' not a postulate

  α : Σ-map (init-Σ-alg X) ΣSuspP
  α = initial (initial-Σ-alg X) ΣSuspP

  π₁∘α=id : (fst ∘ map α) x ≡ x
  π₁∘α=id = cong (λ α → map α x) (unique (initial-Σ-alg X) (π₁ ∘Σ α) idΣ)
