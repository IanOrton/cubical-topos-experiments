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
module interval where 

open import prelude
open import impredicative

----------------------------------------------------------------------
-- Interval
----------------------------------------------------------------------
open import Agda.Builtin.TrustMe
postulate
  Int   : Set
  O     : Int
  I     : Int
  O≠I   : O ≡ I → ∅
  min   : Int → Int → Int
  max   : Int → Int → Int
  cntd   : (P : Int → Ω) → ((i : Int) → prf(P i or ¬(P i))) → P O ≡ P I

minOi=O : (i : Int) → min O i ≡ O
minOi=O i = primTrustMe

minIi=i : (i : Int) → min I i ≡ i
minIi=i i = primTrustMe

miniO=O : (i : Int) → min i O ≡ O
miniO=O i = primTrustMe

miniI=i : (i : Int) → min i I ≡ i
miniI=i i = primTrustMe

maxOi=i : (i : Int) → max O i ≡ i
maxOi=i i = primTrustMe

maxIi=I : (i : Int) → max I i ≡ I
maxIi=I i = primTrustMe

maxiO=i : (i : Int) → max i O ≡ i
maxiO=i i = primTrustMe

maxiI=I : (i : Int) → max i I ≡ I
maxiI=I i = primTrustMe

-- Adding the following rewrites should make proofs using the above identities 
-- easier (more comptational):

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE minOi=O #-}
{-# REWRITE minIi=i #-}
{-# REWRITE miniO=O #-}
{-# REWRITE miniI=i #-}
{-# REWRITE maxOi=i #-}
{-# REWRITE maxIi=I #-}
{-# REWRITE maxiO=i #-}
{-# REWRITE maxiI=I #-}

cntd'  : (P : Int → Ω) → ((i : Int) → prf(P i or ¬(P i))) → (i : Int) → P i ≡ P I
cntd' P dec i = cntd (λ j → P (max i j)) (λ j → dec (max i j))

-- Type for representing just the endpoints O and I
data OI : Set where
  O' : OI
  I' : OI

! : OI → OI
! O' = I'
! I' = O'

!!e=e : (e : OI) → ! (! e) ≡ e
!!e=e O' = refl
!!e=e I' = refl

{-# REWRITE !!e=e #-}

⟨_⟩ : (e : OI) → Int
⟨ O' ⟩ = O
⟨ I' ⟩ = I

cnx : OI → Int → Int → Int
cnx O' = min
cnx 1' = max

cnxeei=e : (e : OI)(i : Int) → cnx e ⟨ e ⟩ i ≡ ⟨ e ⟩
cnxeei=e O' i = refl
cnxeei=e I' i = refl

cnxeie=e : (e : OI)(i : Int) → cnx e i ⟨ e ⟩ ≡ ⟨ e ⟩
cnxeie=e O' i = refl
cnxeie=e I' i = refl

cnx!eei=i : (e : OI)(i : Int) → cnx (! e) ⟨ e ⟩ i ≡ i
cnx!eei=i O' i = refl
cnx!eei=i I' i = refl

cnx!eie=i : (e : OI)(i : Int) → cnx (! e) i ⟨ e ⟩ ≡ i
cnx!eie=i O' i = refl
cnx!eie=i I' i = refl

cnxe!ei=i : (e : OI)(i : Int) → cnx e ⟨ ! e ⟩ i ≡ i
cnxe!ei=i O' i = refl
cnxe!ei=i I' i = refl

cnxei!e=i : (e : OI)(i : Int) → cnx e i ⟨ ! e ⟩ ≡ i
cnxei!e=i O' i = refl
cnxei!e=i I' i = refl

{-# REWRITE cnxeei=e #-}
{-# REWRITE cnxeie=e #-}
{-# REWRITE cnx!eei=i #-}
{-# REWRITE cnx!eie=i #-}
{-# REWRITE cnxe!ei=i #-}
{-# REWRITE cnxei!e=i #-}

e≠!e : {A : Set}{e : OI} → ⟨ e ⟩ ≡ ⟨ ! e ⟩ → A
e≠!e {A} {O'} p = ∅-elim (O≠I p)
e≠!e {A} {I'} p = ∅-elim (O≠I (symm p))

OIinj : (i : Int)(e : OI) → i ≡ ⟨ e ⟩ → (i ≡ O) ⊎ (i ≡ I)
OIinj _ O' p = inl p
OIinj _ I' q = inr q

-- Functions for performing case analysis on endpoints
-- In one variable:
OI-elim :
  {i : Int}
  {B : Set}
  (f : (i ≡ O) ⊎ (i ≡ I) → B)
  → ---------------------------
  prf (i ≈ O or i ≈ I) → B
OI-elim {i} f u = ∥∥-elim f casesAgree u where
  casesAgree : (x x' : (i ≡ O) ⊎ (i ≡ I)) → f x ≡ f x'
  casesAgree (inl i≡O) (inl i≡O') = cong (f ∘ inl) uipImp 
  casesAgree (inl i≡O) (inr i≡I) = ∅-elim (O≠I (trans i≡I (symm i≡O)))
  casesAgree (inr i≡I) (inl i≡O) = ∅-elim (O≠I (trans i≡I (symm i≡O)))
  casesAgree (inr i≡I) (inr i≡I') = cong (f ∘ inr) uipImp

e!e-elim :
  {i : Int}
  {B : Set}
  {e : OI}
  (f : (i ≡ ⟨ e ⟩) ⊎ (i ≡ ⟨ ! e ⟩) → B)
  → ---------------------------
  prf (i ≈ ⟨ e ⟩ or i ≈ ⟨ ! e ⟩) → B
e!e-elim {e = O'} = OI-elim
e!e-elim {i }{e = I'} f u = OI-elim (λ{ (inl x) → f (inr x) ; (inr x) → f (inl x) })
  (∥∥-elim (λ{ (inl x) → ∣ inr x ∣ ; (inr x) → ∣ inl x ∣ }) (λ x x' → eq (i ≈ ⟨ O' ⟩ or i ≈ ⟨ I' ⟩)) u)

-- OI-elim-inl : 
--   {i : Int}
--   {B : Set}
--   (f : (i ≡ O) ⊎ (i ≡ I) → B)
--   (l : i ≡ O)
--   → ---------------------------
--   OI-elim f ∣ inl l ∣ ≡ f (inl l)
-- OI-elim-inl f refl = primTrustMe
-- {-# REWRITE OI-elim-inl #-}

-- OI-elim-inr : 
--   {i : Int}
--   {B : Set}
--   (f : (i ≡ O) ⊎ (i ≡ I) → B)
--   (r : i ≡ I)
--   → ---------------------------
--   OI-elim f ∣ inr r ∣ ≡ f (inr r)
-- OI-elim-inr f refl = primTrustMe
-- {-# REWRITE OI-elim-inr #-}

-- The dependent version:
OI-elim-dep :
  {i : Int}
  {B : prf (i ≈ O or i ≈ I) → Set _}
  (f : (v : (i ≡ O) ⊎ (i ≡ I)) → B ∣ v ∣ )
  → ---------------------------
  (u : prf (i ≈ O or i ≈ I)) → B u
OI-elim-dep {i} {B} f u = OI-elim cases u where
  cases : (i ≡ O) ⊎ (i ≡ I) → B u
  cases (inl i≡O) = subst B (equ (i ≈ O or i ≈ I) ∣ inl i≡O ∣ u) (f (inl i≡O))
  cases (inr i≡I) = subst B (equ (i ≈ O or i ≈ I) ∣ inr i≡I ∣ u) (f (inr i≡I))

-- And in two variables:
OI-elim' :
  {i j : Int}
  {B : Set}
  (f : (i ≡ O) ⊎ (i ≡ I) → B)
  (g : (j ≡ O) ⊎ (j ≡ I) → B)
  (corners : (e e' : OI)(p : i ≡ ⟨ e ⟩)(q : j ≡ ⟨ e' ⟩) → f (OIinj i e p) ≡ g (OIinj j e' q))
  → ---------------------------
  prf ((i ≈ O or i ≈ I) or (j ≈ O or j ≈ I)) → B
OI-elim' {i} {j} {B} f g corners u = ∥∥-elim split corners' u where
  casesAgree : {i : Int}(f : (i ≡ O) ⊎ (i ≡ I) → B)(x x' : (i ≡ O) ⊎ (i ≡ I)) → f x ≡ f x'
  casesAgree f (inl i≡O) (inl i≡O') = cong (f ∘ inl) uipImp 
  casesAgree _ (inl i≡O) (inr i≡I) = ∅-elim (O≠I (trans i≡I (symm i≡O)))
  casesAgree _ (inr i≡I) (inl i≡O) = ∅-elim (O≠I (trans i≡I (symm i≡O)))
  casesAgree f (inr i≡I) (inr i≡I') = cong (f ∘ inr) uipImp 
  split :  prf (i ≈ O or i ≈ I) ⊎ prf (j ≈ O or j ≈ I) → B
  split (inl iOI) = ∥∥-elim f (casesAgree f) iOI
  split (inr jOI) = ∥∥-elim g (casesAgree g) jOI
  corners' : (x x' : prf (i ≈ O or i ≈ I) ⊎ prf (j ≈ O or j ≈ I)) → split x ≡ split x'
  corners' (inl u) (inl v) = cong (λ x → split (inl x)) (equ (i ≈ O or i ≈ I) u v)
  corners' (inl u) (inr v) = or-elim-eq (split ∘ inl) (split (inr v))
    (λ {i≡O} → symm (or-elim-eq (split ∘ inr) (split (inl ∣ inl i≡O ∣))
      (λ {j≡O} → symm (corners O' O' i≡O j≡O))
      (λ {j≡I} → symm (corners O' I' i≡O j≡I)) v))
    ((λ {i≡I} → symm (or-elim-eq (split ∘ inr) (split (inl ∣ inr i≡I ∣))
      (λ {j≡O} → symm (corners I' O' i≡I j≡O))
      (λ {j≡I} → symm (corners I' I' i≡I j≡I)) v)))
    u
  corners' (inr u) (inl v) = or-elim-eq (split ∘ inr) (split (inl v))
    (λ {j≡O} → symm (or-elim-eq (split ∘ inl) (split (inr ∣ inl j≡O ∣))
      (λ {i≡O} → corners O' O' i≡O j≡O)
      (λ {i≡I} → corners I' O' i≡I j≡O) v))
    (λ {j≡I} → symm (or-elim-eq (split ∘ inl) (split (inr ∣ inr j≡I ∣))
      (λ {i≡O} → corners O' I' i≡O j≡I)
      (λ {i≡I} → corners I' I' i≡I j≡I) v))
    u
  corners' (inr u) (inr v) = cong (λ x → split (inr x)) (equ (j ≈ O or j ≈ I) u v)
