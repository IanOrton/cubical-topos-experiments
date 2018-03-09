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
module equivs where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.products
open import Data.paths

----------------------------------------------------------------------
-- Contr and Ext
----------------------------------------------------------------------
Contr' : Set → Set
Contr' A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

Contr : {Γ : Set} → (Γ → Set) → Set
Contr {Γ} A = (x : Γ) → Contr' (A x)

Ext' : Set → Set
Ext' A = (φ : Cof)(f : [ φ ] → A) → ⟦ a ∈ A ∣ (φ , f) ↗ a ⟧

Ext : {Γ : Set} → (Γ → Set) → Set
Ext {Γ} A = (x : Γ) → Ext' (A x)

contr2ext : {Γ : Set}{A : Γ → Set} → isFib A → Contr A → Ext A
contr2ext {Γ} {A} α ap x φ f = (fst a' , (λ u → trans (q u) (p u))) where
  a : A x
  a = fst (ap x)

  c : (a' : A x) → a' ~ a
  c = snd (ap x)

  path : [ φ ] → Int → A x
  path u = fst (c (f u))
  
  a' : ⟦ a' ∈ (A x) ∣ (φ , path) ∙ O ↗ a' ⟧
  a' = α I' (λ _ → x) φ path (a , (λ u → snd (snd (c (f u)))))

  p : (u : [ φ ]) → f u ≡ fst (c (f u)) O
  p u = symm (fst (snd (c (f u))))

  q : (u : [ φ ]) → fst (c (f u)) O ≡ fst a'
  q = snd a'

contr2extFalse : {Γ : Set}{A : Γ → Set}(α : isFib A)(c : Contr A)(x : Γ)
  → fst (contr2ext α c x cofFalse ∅-elim) ≡ fst (α I' (λ _ → x) cofFalse ∅-elim (fst (c x) , (λ ())))
contr2extFalse {Γ} {A} α c x = 
  proof:
      fst (contr2ext α c x cofFalse ∅-elim)
    ≡[ cong (λ hh' → fst (α I' (λ _ → x) cofFalse (fst hh') ((fst (c x)) , snd hh'))) equal ]≡
      fst (α I' (λ _ → x) cofFalse ∅-elim (fst (c x) , (λ ())))
  qed
    where
      path : [ cofFalse ] → Int → A x
      path u = fst (snd (c x) (∅-elim u))
      equal : _≡_ {A = Σ path ∈ ([ cofFalse ] → Int → A x) , prf ((cofFalse , path) ∙ I ↗ fst (c x))} (path , (λ u → snd (snd (snd (c x) (∅-elim u))))) (∅-elim , λ ())
      equal = Σext (funext (λ ())) (funext (λ ()))


ext2fib : {Γ : Set}{A : Γ → Set} → Ext A → isFib A × Contr A
ext2fib {A = A} ext = ((λ e p φ f a → ext (p ⟨ ! e ⟩) φ (λ z → f z ⟨ ! e ⟩)) , c) where
  c : Contr A
  fst (c x) = fst (ext x cofFalse ∅-elim)
  fst (snd (c x) a) i = fst (ext x (i ≈O) (λ _ → a))
  fst (snd (snd (c x) a)) = symm (snd (ext x (O ≈O) (λ _ → a)) refl)
  snd (snd (snd (c x) a)) = cong (λ{(φ , f) → fst (ext x φ f)}) (Σext bothFalse bothElim) where
    bothFalse : I ≈O ≡ cofFalse
    bothFalse = cofEq (propext (O≠I ∘ symm) ∅-elim)
    bothElim : subst (λ z → [ z ] → A x) bothFalse (λ _ → a) ≡ ∅-elim
    bothElim = funext (λ false → ∅-elim false)

----------------------------------------------------------------------
-- Equivalences and quasi-inverses
----------------------------------------------------------------------
Fiber : {A B : Set}(f : A → B)(b : B) → Set
Fiber {A} f b = Σ a ∈ A , f a ~ b

Equiv' : {A B : Set}(f : A → B) → Set
Equiv' {A} {B} f = (b : B) → Contr' (Fiber f b)

Equiv : {Γ : Set}{A B : Γ → Set}(f : (x : Γ) → A x → B x) → Set
Equiv {Γ} f = (x : Γ) → Equiv' (f x)

Qinv : {A B : Set}(f : A → B) → Set
Qinv {A} {B} f = Σ g ∈ (B → A) , ((b : B) → f (g b) ~ b) × ((a : A) → g (f a) ~ a)

fiberext : {A B : Set}{f : A → B}{b : B}{x y : Fiber f b} → fst x ≡ fst y → fst (snd x) ≡ fst (snd y) → x ≡ y
fiberext refl refl = Σext refl (PathExt refl)

-- Singletons are contractible
Sing : {A : Set} → A → Set
Sing {A} a = Σ a' ∈ A , (a' ~ a)

singExt : {A : Set}{a : A}{s s' : Sing a} → fst (snd s) ≡ fst (snd s') → s ≡ s'
singExt {s = (_ , _ , refl , refl)} {s' = (_ , _ , refl , refl)} refl = refl

singContr : {A : Set}(a : A) → Contr' (Sing a)
fst (singContr {A} a) = a , reflPath' refl
fst (fst (snd (singContr a) (a' , p)) i) = fst p i
fst (snd (fst (snd (singContr a) (a' , p)) i)) j = fst p (max i j)
fst (snd (snd (fst (snd (singContr a) (a' , p)) i))) = refl
snd (snd (snd (fst (snd (singContr a) (a' , p)) i))) = snd (snd p)
fst (snd (snd (singContr a) (a' , p))) = singExt refl
snd (snd (snd (singContr a) (a' , p))) = singExt (funext (λ j → snd (snd p)))

-- The identity map is an equivalence
idEquiv : {A : Set} → Equiv' {A} id
idEquiv a = singContr a

-- This is a standard result in HoTT.
postulate
 qinv2equiv :
  {Γ : Set}{A B : Γ → Set}(α : isFib A)(β : isFib B)
  (f : (x : Γ) → A x → B x) → ((x : Γ) → Qinv (f x)) → Equiv f

