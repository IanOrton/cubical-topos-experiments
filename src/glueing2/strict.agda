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
module glueing2.strict where 

open import glueing2.core

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import equivs
open import Data.paths
open import Data.products

----------------------------------------------------------------------
-- Strictifying
----------------------------------------------------------------------
record _≅'_(A B : Set) : Set where
 field
  f : A → B
  g : B → A
  inv₁ : g ∘ f ≡ id
  inv₂ : f ∘ g ≡ id

postulate
 reIm :
  (φ : Cof)
  (A : [ φ ] → Set)
  (B : Set)
  (m : (u : [ φ ]) → A u ≅' B)
  -> ----------------------
  Σ B' ∈ Set , Σ m' ∈ B' ≅' B , ((u : [ φ ]) → (A u , m u) ≡ (B' , m'))

strictify :
  (Φ : Cof)
  (A : [ Φ ] → Set)
  (B : Set)
  (m : (u : [ Φ ]) → A u ≅' B)
  -> ----------------------
  Set
strictify Φ A B m = fst (reIm Φ A B m)

isoB :
  (Φ : Cof)
  (A : [ Φ ] → Set)
  (B : Set)
  (m : (u : [ Φ ]) → A u ≅' B)
  -> ----------------------
  strictify Φ A B m ≅' B
isoB Φ A B m = fst (snd (reIm Φ A B m))
  
restrictsToA :
  (Φ : Cof)
  (A : [ Φ ] → Set)
  (B : Set)
  (m : (u : [ Φ ]) → A u ≅' B)
  (u : [ Φ ])
  -> ----------------------
  A u ≡ strictify Φ A B m
restrictsToA Φ A B m u = Σeq₁ (snd (snd (reIm Φ A B m)) u)
  
restrictsToM :
  (Φ : Cof)
  (A : [ Φ ] → Set)
  (B : Set)
  (m : (u : [ Φ ]) → A u ≅' B)
  (u : [ Φ ])
  -> ----------------------
  (A u , m u) ≡ (strictify Φ A B m , isoB Φ A B m)
restrictsToM Φ A B m u = snd (snd (reIm Φ A B m)) u

-- ----------------------------------------------------------------------
-- -- Strict glueing
-- ----------------------------------------------------------------------
SGlue :
  (Φ : Cof)
  (A : [ Φ ] → Set)
  (B : Set)
  (f : (u : [ Φ ]) → A u → B)
  → ---------------
  Set

private
 fIso :
  (Φ : Cof)
  {A : [ Φ ] → Set}
  {B : Set}
  (w : (u : [ Φ ]) → A u → B)
  → ---------------
  (u : [ Φ ]) → A u ≅' Glue Φ A B w
abstract
 fIso Φ {A} {B} w u = iso where
  open _≅'_
  prfIr : {a : A u} → subst A (equ (fst Φ) u u) a ≡ a
  prfIr {a} =
    let switch = uip (equ (fst Φ) u u) refl in
    cong (λ p → subst A p a) switch
  iso : A u ≅' Glue Φ A B w
  f iso a = glue {Φ = Φ} w u a
  g iso (a , _ , _) = a u
  inv₁ iso = funext (λ a → prfIr)
  inv₂ iso = funext fg≡id where
    parEq : {a a' : (u : [ Φ ]) → A u} → a u ≡ a' u → a ≡ a'
    parEq {a} {a'} eq = funext (λ v → subst (λ v → a v ≡ a' v) (equ (fst Φ) u v) eq)
    fg≡id : (gl : Glue Φ A B w) → (glue {Φ = Φ} w u (fst gl u)) ≡ gl
    fg≡id gl = glueExt {Φ = Φ} w (glue {Φ = Φ} w u (fst gl u)) gl fstEq sndEq where
      fstEq : fst (glue {Φ = Φ} w u (fst gl u)) ≡ fst gl
      fstEq = parEq prfIr
      sndEq : w u (fst gl u) ≡ fst (snd gl)
      sndEq = snd (snd gl) u
  
SGlue Φ A B w = strictify Φ A (Glue Φ A B w) (fIso Φ w)

-- sglue :
--   {Γ : Set}
--   {Φ : Γ → Cof}
--   {A : res Γ Φ → Set}
--   {B : Γ → Set}
--   (w : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
--   → ---------------
--   (xu : res Γ Φ) → A xu → SGlue Φ A B w (fst xu)
-- abstract
--  sglue {Γ} {Φ} {A} {B} w (x , u) = (_≅'_.g iso) ∘ glue {Φ = Φ} w (x , u) where
--   iso : SGlue Φ A B w x ≅' Glue Φ A B w x
--   iso = isoB Φ A (Glue Φ A B w) (fIso Φ w) x

-- sunglue :
--   {Γ : Set}
--   {Φ : Γ → Cof}
--   {A : res Γ Φ → Set}
--   {B : Γ → Set}
--   (w : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
--   → ---------------
--   (x : Γ) → SGlue Φ A B w x → B x
-- abstract
--  sunglue {Γ} {Φ} {A} {B} w x = (unglue {Φ = Φ} w x) ∘ _≅'_.f iso where
--   iso : SGlue Φ A B w x ≅' Glue Φ A B w x
--   iso = isoB Φ A (Glue Φ A B w) (fIso Φ w) x

-- FibSGlue' :
--   {Γ : Set}
--   {Φ : Γ → Cof}
--   {A : res Γ Φ → Set}
--   {B : Γ → Set}
--   (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
--   (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
--   → ---------------
--   isFib A → isFib B → isFib (SGlue Φ A B f)
-- abstract
--  FibSGlue' {Γ} {Φ} {A} {B} f equiv α β =
--   FibIso (Glue Φ A B f) (SGlue Φ A B f) iso (FibGlue {Φ = Φ} f equiv α β) where
--     iso : Glue Φ A B f ≅ SGlue Φ A B f
--     iso x = (_≅'_.g iso' , _≅'_.f iso' , (_≅'_.inv₂ iso' , _≅'_.inv₁ iso')) where
--       iso' : SGlue Φ A B f x ≅' Glue Φ A B f x
--       iso' = isoB Φ A (Glue Φ A B f) (fIso Φ f) x

-- SGlueFib' :
--   {Γ : Set}
--   (Φ : Γ → Cof)
--   (A : Fib (res Γ Φ))
--   (B : Fib Γ)
--   (f : (x : Γ)(u : [ Φ x ]) → fst A (x , u) → fst B x)
--   (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
--   → --------------
--   Fib Γ
-- SGlueFib' {Γ} Φ (A , α) (B , β) f equiv = SGlue Φ A B f , FibSGlue' {Γ} {Φ} {A} {B} f equiv α β

strictness :
  (Φ : Cof)
  (A : [ Φ ] → Set)
  (B : Set)
  (f : (u : [ Φ ]) → A u → B)
  (u : [ Φ ])
  → ---------------
  SGlue Φ A B f ≡ A u
abstract
 strictness Φ A B f u = symm (restrictsToA Φ A (Glue Φ A B f) (fIso Φ f) u)

-- str :
--   {Γ : Set}
--   {Φ : Γ → Cof}
--   {A : res Γ Φ → Set}
--   {B : Γ → Set}
--   (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
--   (x : Γ)
--   → ---------------
--   Glue Φ A B f x → SGlue Φ A B f x
-- abstract
--  str {Γ} {Φ} {A} {B} f x = _≅'_.g (isoB Φ A (Glue Φ A B f) (fIso Φ f) x)

-- unstr :
--   {Γ : Set}
--   {Φ : Γ → Cof}
--   {A : res Γ Φ → Set}
--   {B : Γ → Set}
--   (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
--   (x : Γ)
--   → ---------------
--   SGlue Φ A B f x → Glue Φ A B f x
-- abstract
--  unstr {Γ} {Φ} {A} {B} f x = _≅'_.f (isoB Φ A (Glue Φ A B f) (fIso Φ f) x)

-- unstrIsGlue :
--   {Γ : Set}
--   {Φ : Γ → Cof}
--   {A : res Γ Φ → Set}
--   {B : Γ → Set}
--   (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
--   (x : Γ)
--   (u : [ Φ x ])
--   → ---------------
--   (a : SGlue Φ A B f x ) → unstr {Γ} {Φ} {A} {B} f x a ≡ glue {Φ = Φ} f (x , u) (coe (strictness Φ A B f x u) a)
-- abstract
--  unstrIsGlue {Γ} {Φ} {A} {B} f x u g = inner (restrictsToM Φ A (Glue Φ A B f) (fIso Φ f) x u) g where
--   inner : {Am Gs : Σ X ∈ Set , X ≅' Glue Φ A B f x}(eq : Am ≡ Gs)(g : fst Gs) → _≅'_.f (snd Gs) g ≡ _≅'_.f (snd Am) (coe (symm (Σeq₁ eq)) g)
--   inner refl b = refl

-- strIsUnglue :
--   {Γ : Set}
--   {Φ : Γ → Cof}
--   {A : res Γ Φ → Set}
--   {B : Γ → Set}
--   (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
--   (x : Γ)
--   (u : [ Φ x ])
--   → ---------------
--   (g : Glue Φ A B f x) → str {Γ} {Φ} {A} {B} f x g ≡ coe (symm (strictness Φ A B f x u)) (fst g u)
-- abstract
--  strIsUnglue {Γ} {Φ} {A} {B} f x u g = inner (restrictsToM Φ A (Glue Φ A B f) (fIso Φ f) x u) g where
--   inner : {Am Gs : Σ X ∈ Set , X ≅' Glue Φ A B f x}(eq : Am ≡ Gs)(g : Glue Φ A B f x) → _≅'_.g (snd Gs) g ≡ coe (symm (symm (Σeq₁ eq))) (_≅'_.g (snd Am) g)
--   inner refl b = refl

-- unstrStr :
--   {Γ : Set}
--   {Φ : Γ → Cof}
--   {A : res Γ Φ → Set}
--   {B : Γ → Set}
--   (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
--   (x : Γ)
--   → ---------------
--   (unstr {Γ} {Φ} {A} {B} f x) ∘ (str {Γ} {Φ} {A} {B} f x) ≡ id
-- abstract
--  unstrStr {Γ} {Φ} {A} {B} f x = _≅'_.inv₂ (isoB Φ A (Glue Φ A B f) (fIso Φ f) x)

-- strUnstr :
--   {Γ : Set}
--   {Φ : Γ → Cof}
--   {A : res Γ Φ → Set}
--   {B : Γ → Set}
--   (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
--   (x : Γ)
--   → ---------------
--   (str {Γ} {Φ} {A} {B} f x) ∘ (unstr {Γ} {Φ} {A} {B} f x) ≡ id
-- abstract
--  strUnstr {Γ} {Φ} {A} {B} f x = _≅'_.inv₁ (isoB Φ A (Glue Φ A B f) (fIso Φ f) x)


-- uaβhelper2 :
--   {Γ : Set}
--   (A : Fib (res (Γ × Int) i=OI))
--   (B : Fib (Γ × Int))
--   (f : (x : Γ × Int)(u : [ i=OI x ]) → fst A (x , u) → fst B x)
--   (equiv : (x : Γ × Int)(v : [ i=OI x ]) → Equiv' (f x v))
--   (x : Γ)
--   (a : SGlue i=OI (fst A) (fst B) f (x , O))
--   → ---------------
--   fst (FibSGlue' f equiv (snd A) (snd B) O' < x ,id> cofFalse ∅-elim (a , λ ()))
--     ≡ str f (x , I) (fst (FibGlue {Φ = i=OI} f equiv (snd A) (snd B) O' < x ,id> cofFalse ∅-elim ((unstr f (x , O) a) , (λ ()))))
-- abstract
--  uaβhelper2 (A , α) (B , β) f equiv x a = trivialFibIso (Glue i=OI A B f) (SGlue i=OI A B f) iso (FibGlue {Φ = i=OI} f equiv α β) < x ,id> a where
--     iso : Glue i=OI A B f ≅ SGlue i=OI A B f
--     iso x = (_≅'_.g iso' , _≅'_.f iso' , (_≅'_.inv₂ iso' , _≅'_.inv₁ iso')) where
--       iso' : SGlue i=OI A B f x ≅' Glue i=OI A B f x
--       iso' = isoB i=OI A (Glue i=OI A B f) (fIso i=OI f) x
