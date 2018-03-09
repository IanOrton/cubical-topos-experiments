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

module impredicative.logic where

open import prelude
open import impredicative.prop public

infix  1 exists all exists!
infixr 3 _⊃_ _or_ _&_
infix  4 _≈_ 

----------------------------------------------------------------------
-- Function extensionality using primTrustMe
----------------------------------------------------------------------
open import Agda.Builtin.TrustMe

funext :
   {ℓ  ℓ' : Level}
   {A : Set ℓ}
   {B : A → Set ℓ'}
   {f g : (x : A) → B x}
   → ----------------------------
   ((x : A) → f x ≡ g x) → f ≡ g
funext _ = primTrustMe

----------------------------------------------------------------------
-- Proposition extensionality using primTrustMe
----------------------------------------------------------------------
propext :
  {P Q : Ω}
  → ---------------------------------------
  (prf P → prf Q) → (prf Q → prf P) → P ≡ Q
propext _ _ = primTrustMe

----------------------------------------------------------------------
-- Comprehension
----------------------------------------------------------------------
set : ∀ {a} (A : Set a)(P : A → Ω) → Set a
set A P = Σ x ∈ A , prf (P x)

inc : {A : Set}(P : A → Ω) → set A P → A
inc _ = fst 

syntax set A (λ x → P) = ⟦ x ∈ A ∣ P ⟧

incMono :
   {A : Set}
   (P : A → Ω)
   → -----------------------------------------
   (a b : set A P) → inc P a ≡ inc P b → a ≡ b
incMono P (x , u) (.x , v) refl = cong (_,_ x) (equ (P x) u v)

----------------------------------------------------------------------
-- Equality 
----------------------------------------------------------------------
_≈_ : {A : Set} → A → A → Ω 
prf (x ≈ y) = x ≡ y
equ (_ ≈ _) = uip 

----------------------------------------------------------------------
-- Universal quantifier
----------------------------------------------------------------------
all : (A : Set) → (A → Ω) → Ω
prf (all A P)     = (x : A) → prf (P x)
equ (all A P) f g = funext (λ x → equ (P x) (f x) (g x))

syntax all A (λ x → P) = All x ∈ A , P

----------------------------------------------------------------------
-- Implication
----------------------------------------------------------------------
_⊃_ : Ω → Ω → Ω
P ⊃ Q = All _ ∈ prf P , Q

----------------------------------------------------------------------
-- Truth
----------------------------------------------------------------------
⊤ : Ω
prf ⊤ = Unit
equ ⊤ tt tt = refl

----------------------------------------------------------------------
-- Conjunction
----------------------------------------------------------------------
_&_ : Ω → Ω → Ω
prf (P & Q)                     = prf P × prf Q
equ (P & Q) (u₁ , u₂) (v₁ , v₂) =
  Σext (equ P u₁ v₁)
  (equ Q (subst (λ _ → prf Q) (equ P u₁ v₁) u₂) v₂)

----------------------------------------------------------------------
-- Falsity
----------------------------------------------------------------------
⊥ : Ω
prf ⊥  = ∅
equ ⊥ () _

----------------------------------------------------------------------
-- Negation
----------------------------------------------------------------------
¬ : Ω → Ω
¬ P = P ⊃ ⊥

----------------------------------------------------------------------
-- Propositional truncation
----------------------------------------------------------------------
∥_∥ : Set → Ω
prf ∥ A ∥     = (P : Ω) → (A → prf P) → prf P
equ ∥ A ∥ f g = funext (λ P → funext (λ h → equ P (f P h) (g P h)))

∣_∣ : {A : Set} → A → prf ∥ A ∥
∣ x ∣ _ f = f x

∥∥-rec :
  {A : Set}
  (P : Ω)
  (f : A → prf P)
  → ---------------
  prf ∥ A ∥ → prf P
∥∥-rec P f u = u P f

----------------------------------------------------------------------
-- Disjunction
----------------------------------------------------------------------
_or_ : Ω → Ω → Ω
P or Q =  ∥ prf P ⊎ prf Q ∥

orl : {P Q : Ω} → prf P → prf (P or Q)
orl = λ u _ v → v (inl u)

orr : {P Q : Ω} → prf Q → prf (P or Q)
orr = λ u _ v → v (inr u)

----------------------------------------------------------------------
-- Existential quantifier
----------------------------------------------------------------------
exists : (A : Set) → (A → Ω) → Ω
exists A P = ∥ Σ x ∈ A , prf (P x) ∥

syntax exists A (λ x → P) = ∃ x ∈ A , P

----------------------------------------------------------------------
-- More general form of ∥∥-rec
----------------------------------------------------------------------
∥∥-elim :
  {A B : Set}
  (f : A → B)
  (e : (x x' : A) → f x ≡ f x')
  → ---------------------------
  prf ∥ A ∥ → B

∥∥-elim {A} {B} f e u = fst (u Pf q) where
  Imf : Set
  Imf = ⟦ y ∈ B ∣ ∃ x ∈ A , f x ≈ y ⟧

  q : A → Imf
  fst (q x)     = f x
  snd (q x) _ g = g (x , refl)

  lem1 :
    (y y' : B)
    → ---------------------------------------------------
    (Σ x ∈ A , f x ≡ y) → (Σ x' ∈ A , f x' ≡ y') → y ≡ y'
  lem1 y y' (x , u) (x' , u' ) =
    proof:
      y
        ≡[ symm u ]≡
      f x
        ≡[ e x x' ]≡
      f x'
        ≡[ u' ]≡
      y'
    qed
    
  lem2 :
    (y y' : B)
    → -----------------------------------------------------------
    prf (∃ x ∈ A , f x ≈ y) → prf (∃ x' ∈ A , f x' ≈ y') → y ≡ y'
  lem2 y y' =
    ∥∥-rec (exists A (λ x' → f x' ≈ y') ⊃ y ≈ y') λ z  →
    ∥∥-rec (y ≈ y') λ z' → lem1 y y' z z'
  
  Pf : Ω
  prf Pf                   = Imf
  equ Pf (y , v) (y' , v') = Σext (lem2 y y' v v')
                            (eq (exists A (λ x' → f x' ≈ y')))

----------------------------------------------------------------------
-- or-elim
----------------------------------------------------------------------
or-elim :
  {A B : Set}
  (C : prf ∥ A ⊎ B ∥ → Set)
  (is-prop : (u : prf ∥ A ⊎ B ∥) → (c c' : C u) → c ≡ c')
  (p : (a : A) → C ∣ inl a ∣)
  (q : (b : B) → C ∣ inr b ∣)
  → ---------------------------
  (u : prf ∥ A ⊎ B ∥) → C u
or-elim {A} {B} C is-prop p q u = ∥∥-elim cases (λ x y → is-prop u (cases x) (cases y)) u where
  cases : A ⊎ B → C u
  cases (inl a) = subst C (eq ∥ A ⊎ B ∥) (p a)
  cases (inr b) = subst C (eq ∥ A ⊎ B ∥) (q b)


or-elim-eq :
  {A B C : Set}
  (f : prf ∥ A ⊎ B ∥ → C)
  (c : C)
  (p : {l : A} → f ∣ inl l ∣ ≡ c)
  (q : {r : B} → f ∣ inr r ∣ ≡ c)
  → ---------------------------
  (u : prf ∥ A ⊎ B ∥) → f u ≡ c

or-elim-eq {A} {B} {C} f c p q u = ∥∥-elim cases uip' u where
  cases : A ⊎ B → f u ≡ c
  cases (inl l) = subst (λ u → f u ≡ c) (equ ∥ A ⊎ B ∥ ∣ inl l ∣ u) p
  cases (inr r) = subst (λ u → f u ≡ c) (equ ∥ A ⊎ B ∥ ∣ inr r ∣ u) q
  uip' : (x x' : A ⊎ B) → cases x ≡ cases x'
  uip' x x' = uip (cases x) (cases x')

----------------------------------------------------------------------
-- Unique existence
----------------------------------------------------------------------
exists! : (A : Set) → (A → Ω) → Ω
exists! A P = ∃ x ∈ A , P x & (All x' ∈ A , P x' ⊃ x ≈ x')

syntax exists! A (λ x → P) = ∃! x ∈ A , P

----------------------------------------------------------------------
-- Axiom of description
----------------------------------------------------------------------
axd :
  {A : Set}
  (P : A → Ω)
  → ----------------------------------------
  prf (∃! x ∈ A , P x) → Σ x ∈ A , prf (P x)

axd {A} P u = ∥∥-elim f e u where

  B : Set
  B = Σ x ∈ A , prf (P x) × ((x' : A) → prf (P x') → x ≡ x')
  
  f : B → (Σ x ∈ A , prf (P x))
  f (x , u , _) = (x , u)

  e : (y y' : B) → f y ≡ f y'
  e (_ , _ , g) (x' , u' , _) = Σext (g x' u') (eq (P x'))

