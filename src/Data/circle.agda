{-# OPTIONS --rewriting #-}

module Data.circle where

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

record S¹-alg : Set₁ where
 field
  obj : Set
  h   : isFibObj obj
  ba  : obj
  lo  : ba ~ ba

open S¹-alg

record S¹-map (A B : S¹-alg) : Set where
 field
  map    : obj A → obj B
  b-pres : map (ba A) ≡ ba B
  l-pres : (i : Int) → map (lo A at i) ≡ (lo B) at i
  h-pres :
    (e : OI)
    (φ : Cof)
    (f : [ φ ] → Int → obj A)
    (x₀ : ⟦ x₁ ∈ obj A ∣ (φ , f) ∙ ⟨ e ⟩ ↗ x₁ ⟧)
    → -----------------------
    map (fst (h A e φ f x₀)) ≡ fst (h B e φ (λ u i → map (f u i)) (lift φ map x₀))

open S¹-map

idS¹ : {A : S¹-alg} → S¹-map A A
map idS¹ = id
b-pres idS¹ = refl
l-pres idS¹ _ = refl
h-pres (idS¹ {A}) e φ f x = cong (λ x → fst (h A e φ f x)) (Σext refl (funext λ u → symm cong-id)) where
  cong-id : {A : Set}{x y : A}{p : x ≡ y} → cong id p ≡ p
  cong-id {p = refl} = refl

_∘S¹_ : {A B C : S¹-alg}(g :  S¹-map B C)(f :  S¹-map A B) →  S¹-map A C
map (β ∘S¹ α) = map β ∘ map α
b-pres (_∘S¹_ {C = C} β α) = subst (λ x → map β x ≡ ba C) (symm (b-pres α)) (b-pres β)
l-pres (_∘S¹_ {C = C} β α) i = subst (λ x → map β x ≡ lo C at i) (symm (l-pres α i)) (l-pres β i)
h-pres (_∘S¹_ {C = C} β α) e φ f x₀ =
  trans
    (cong (λ x → fst (h C e φ (λ u i → map β (map α (f u i))) x)) (Σext refl (funext λ _ → uipImp)))
    (trans
      (h-pres β e φ (λ u i → map α (f u i)) (lift φ (map α) x₀))
      (cong (map β) (h-pres α e φ f x₀))
    )

record Initial-S¹-alg : Set₁ where
 field
  Alg     : S¹-alg
  initial : (B : S¹-alg) → S¹-map Alg B
  unique  : {B : S¹-alg}(α β : S¹-map Alg B) → α ≡ β

open Initial-S¹-alg

postulate
  initial-S¹-alg : Initial-S¹-alg

𝕊¹-alg : S¹-alg
𝕊¹-alg = Alg initial-S¹-alg

𝕊¹ : Set
𝕊¹ = obj 𝕊¹-alg

base : 𝕊¹
base = ba 𝕊¹-alg

loop : base ~ base
loop = lo 𝕊¹-alg

open import Agda.Builtin.TrustMe

𝕊¹-elim :
  (P : 𝕊¹ → Set)
  (ρ : isFib P)
  (a : P base)
  (l : (i : Int) → P (loop at i))
  (lO : subst P (atO loop) (l O) ≡ a)
  (lI : subst P (atI loop) (l I) ≡ a)
  → ---------------------
  (x : 𝕊¹) → P x
𝕊¹-elim P ρ a l lO lI x = subst P π₁∘α=id (snd (map α x)) where

  Σ𝕊¹P : S¹-alg
  obj Σ𝕊¹P = Σ x ∈ 𝕊¹ , P x
  h Σ𝕊¹P = ΣFib' (h 𝕊¹-alg) ρ
  ba Σ𝕊¹P = base , a
  fst (lo Σ𝕊¹P) i = loop at i , l i
  fst (snd (lo Σ𝕊¹P)) = Σext (atO loop) lO
  snd (snd (lo Σ𝕊¹P)) = Σext (atI loop) lI

  π₁ : S¹-map Σ𝕊¹P 𝕊¹-alg
  map π₁ = fst
  b-pres π₁ = refl
  l-pres π₁ i = refl
  h-pres π₁ e φ f x₀ = primTrustMe  -- Should be provable once ΣFib' not a postulate

  α : S¹-map 𝕊¹-alg Σ𝕊¹P
  α = initial initial-S¹-alg Σ𝕊¹P

  π₁∘α=id : (fst ∘ map α) x ≡ x
  π₁∘α=id = cong (λ α → map α x) (unique initial-S¹-alg (π₁ ∘S¹ α) idS¹)
