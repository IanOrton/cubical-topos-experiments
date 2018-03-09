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
module replacefam where 

open import Agda.Builtin.TrustMe
open import prelude
open import impredicative
open import interval
open import cof
open import fibrations


----------------------------------------------------------------------
-- Lemmas about subst
----------------------------------------------------------------------
substcancel :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  (B : A → Set ℓ')
  {x y : A}
  (f : (a : A) → B a)
  (p : x ≡ y)
  {z : A}
  (q : x ≡ z)
  (r : y ≡ z)
  → ------------------------
  subst B q (f x) ≡ subst B r (f y)
substcancel _ _ refl refl refl = refl

substtrans :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  (B : A → Set ℓ')
  {x y z : A}
  (p : x ≡ y)
  (q : y ≡ z)
  (r : x ≡ z)
  (b : B x)
  → ------------------------
  subst B q (subst B p b)  ≡ subst B r b
substtrans _ refl refl refl _ = refl

substcong :
  {ℓ ℓ' : Level}
  {A A' : Set ℓ}
  (B : A' → Set ℓ')
  (f : A → A')
  {x y : A}
  (p : x ≡ y)
  (b : B (f x))
  → ------------------------
  subst (B ∘ f) p b ≡ subst B (cong f p) b
substcong _ _ refl _ = refl

----------------------------------------------------------------------
-- Quoitents
----------------------------------------------------------------------
infix 6 _/_ [_]/_
postulate
  -- quotient formation
  _/_ : {ℓ ℓ' : Level}(A : Set ℓ)(R : A → A → Set ℓ') → Set (ℓ ⊔ ℓ')
  
  -- quotient introduction
  [_]/_ : {ℓ ℓ' : Level}{A : Set ℓ} → A → (R : A → A → Set ℓ') → A / R

  -- generating equalities
  qeq :
    {ℓ ℓ' : Level}
    {A : Set ℓ}
    {x y : A}
    (R : A → A → Set ℓ')
    (r : R x y)
    → ------------------
    [ x ]/ R ≡ [ y ]/ R

  -- quotient induction
  qind :
    {ℓ ℓ' ℓ'' : Level}
    {A : Set ℓ}
    (R : A → A → Set ℓ')
    (B : A / R → Set ℓ'')
    (f : (x : A) → B ([ x ]/ R))
    (e : (x y : A)(r : R x y) → subst B (qeq R r) (f x) ≡ f y)
    → --------------------------------------------------------
    (y : A / R) → B y

  -- quotient computation
  qind-comp :
    {ℓ ℓ' ℓ'' : Level}
    {A : Set ℓ}
    (R : A → A → Set ℓ')
    (B : A / R → Set ℓ'')
    (f : (x : A) → B ([ x ]/ R))
    (e : (x y : A)(r : R x y) → subst B (qeq R r) (f x) ≡ f y)
    (x : A)
    → --------------------------------------------------------
    qind R B f e ([ x ]/ R) ≡ f x

{-# REWRITE qind-comp   #-}

-- N.B. Not sure if these are correct:
{-# POLARITY _/_ * * ++ ++ #-}
{-# POLARITY [_]/_ * * _ * _ #-}

----------------------------------------------------------------------
-- Fibrant replacement of an family
----------------------------------------------------------------------
mutual
  -- FreeComps A is the result of freely adding compositions to A
  data FreeComps {Γ : Set}(A : Γ → Set) : Γ → Set where
    pure : {x : Γ} → A x → FreeComps A x
    comp :
      (e : OI)
      (p : Int → Γ)
      (φ : Cof)
      (f : [ φ ] → Π ((Replace A) ∘ p))
      (a₀ : ⟦ a₀ ∈ Replace A (p ⟨ e ⟩) ∣ (φ , f) ∙ ⟨ e ⟩ ↗ a₀ ⟧)
      → FreeComps A (p ⟨ ! e ⟩)

  -- Replace A is FreeComps A where we quotient by the equation:
  --     comp e cofTrue f a₀ = f tt
  -- i.e. we ensure that compositions always extend their partial input
  Replace : {Γ : Set}(A : Γ → Set) → Γ → Set
  Replace A x = FreeComps A x / TotalComps

  -- TotalComps is the inductive family describing the necessary relation
  data TotalComps {Γ : Set}{A : Γ → Set} : {x : Γ} → FreeComps A x → FreeComps A x → Set where
    total :
      (e : OI)
      (p : Int → Γ)
      (φ : Cof)
      (f : [ φ ] → Π ((Replace A) ∘ p))
      (a₀ : ⟦ a₀ ∈ Replace A (p ⟨ e ⟩) ∣ (φ , f) ∙ ⟨ e ⟩ ↗ a₀ ⟧)
      (u : [ φ ])
      (a : FreeComps A (p ⟨ ! e ⟩))
      (_ : [ a ]/ TotalComps ≡ f u ⟨ ! e ⟩)
      → TotalComps a (comp e p φ f a₀)

-- The inclusion of A in Replace A
ι : {Γ : Set}{A : Γ → Set}{x : Γ} → A x → Replace A x
ι a = [ pure a ]/ TotalComps

-- -- Replace A is always a fibrant object
replaceIsFib : {Γ : Set}(A : Γ → Set) → isFib (Replace A)
replaceIsFib A e p φ f a₀ = [ comp e p φ f a₀ ]/ TotalComps , ext where
  ext : (u : [ φ ]) → f u ⟨ ! e ⟩ ≡ [ comp e p φ f a₀ ]/ TotalComps
  ext u = qind TotalComps
    (λ a → (_ : a ≡ f u ⟨ ! e ⟩) → a ≡ [ comp e p φ f a₀ ]/ TotalComps)
    (λ a eq → qeq TotalComps (total e p φ f a₀ u a eq))
    (λ _ _ _ → funext (λ _ → uip _ _))
    (f u ⟨ ! e ⟩) refl

-- -- We get a principle for eliminating into fibrant objects
replaceElim :
  {Γ : Set}
  (A : Γ → Set)
  (B : Γ → Set)(β : isFib B)
  (f : (x : Γ) → A x → B x)
  → --------------------
  (x : Γ) → Replace A x → B x

-- -- We need to mark this as terminating, but this should (hopefully) be ok
{-# TERMINATING #-}
replaceElim {Γ} A B β f = elim where
  elim : (x : Γ) → Replace A x → B x
  f' : (ρ : Γ)(x : FreeComps A ρ) → B ρ
  resp : (ρ : Γ)(x y : FreeComps A ρ)(r : TotalComps x y) → subst (λ _ → B ρ) (qeq TotalComps r) (f' ρ x) ≡ f' ρ y
  elim ρ = qind TotalComps (λ _ → B ρ) (f' ρ) (resp ρ)
  f' ρ (pure x) = f ρ x
  f' _ (comp e p φ g (a₀ , ext)) = fst (β e p φ (λ u i → elim (p i) (g u i))
    (elim (p ⟨ e ⟩) a₀ , λ u → cong (qind TotalComps (λ _ → B (p ⟨ e ⟩)) (f' (p ⟨ e ⟩)) (resp (p ⟨ e ⟩))) (ext u)))
  resp _ a .(comp e p φ g (a₀ , ext)) (total e p φ g (a₀ , ext) u .a eq) =
    proof:
      subst (λ _ → B (p ⟨ ! e ⟩)) (qeq TotalComps (total e p φ g (a₀ , ext) u a eq)) (f' (p ⟨ ! e ⟩) a)
        ≡[ substconst _ (qeq TotalComps (total e p φ g (a₀ , ext) u a eq)) (f' (p ⟨ ! e ⟩) a) ]≡
      f' (p ⟨ ! e ⟩) a
        ≡[ cong (elim (p ⟨ ! e ⟩)) eq ]≡
      elim (p ⟨ ! e ⟩) (g u ⟨ ! e ⟩)
        ≡[ snd (β e p φ (λ u i → elim (p i) (g u i))
             (elim (p ⟨ e ⟩) a₀ , λ u → cong (qind TotalComps (λ _ → B (p ⟨ e ⟩)) (f' (p ⟨ e ⟩)) (resp (p ⟨ e ⟩))) (ext u))) u ]≡
      fst (β e p φ (λ u i → elim (p i) (g u i))
        (elim (p ⟨ e ⟩) a₀ , λ u → cong (qind TotalComps (λ _ → B (p ⟨ e ⟩)) (f' (p ⟨ e ⟩)) (resp (p ⟨ e ⟩))) (ext u)))
        ≡[ refl ]≡
      f' (p ⟨ ! e ⟩) (comp e p φ g (a₀ , ext))
    qed

replaceNotNatural :
  --- There exsit
  Σ Δ ∈ Set , Σ Γ ∈ Set ,
  Σ A ∈ (Γ → Set) , 
  Σ f ∈ (Δ → Γ) ,
  --- such that
  (((Replace A) ∘ f ≡ Replace (A ∘ f)) → ∅)
replaceNotNatural = Unit , Int , _≡_ O , (λ _ → I) , contra where
  -- The first type is inhabited because we get something in the i ≡ I
  -- fiber of Replace (_≡_ O) by transporting refl from the i ≡ O fiber
  rO : Replace (_≡_ O) O
  rO = ι refl
  rI : Replace (_≡_ O) I
  rI = fst (replaceIsFib _ O' id cofFalse (λ ()) (rO , (λ ())))
  -- The second type is not inhabited since it is the fibrant
  -- replacement of an uninhabited type:
  uninh : Replace (λ _ → O ≡ I) tt → ∅
  uninh = replaceElim _ _ Fib∅ (λ _ → O≠I) tt
  -- Therefore we get a contradiction from the fact that the two
  -- types are equal
  contra : (Replace (_≡_ O)) ∘ (λ _ → I) ≡ Replace (λ _ → O ≡ I) → ∅
  contra p = uninh (coe (appCong p) rI)
