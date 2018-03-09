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
module Data.products where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
  
----------------------------------------------------------------------
-- Dependent products
----------------------------------------------------------------------
Σ' : ∀{a}{Γ : Set a}(A : Γ → Set)(B : (Σ x ∈ Γ , A x) → Set) → Γ → Set
Σ' A B x = Σ a ∈ A x , B (x , a)

abstract
 FibΣid :
  {A : Int → Set}
  {B : (Σ x ∈ Int , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Σ' A B)
 FibΣid {A} {B} α β e p φ f ((a₀ , b₀) , extendsF) = (fst a₁ , b₁') , extendsAt1 where
  g : [ φ ] → Π (A ∘ p)
  g u i = fst (f u i)

  a₀ExtendsG : prf ((φ , g) ∙ ⟨ e ⟩ ↗ a₀)
  a₀ExtendsG u = cong fst (extendsF u)

  a₁ : ⟦ a ∈ (A ∘ p) ⟨ ! e ⟩ ∣ (φ , g) ∙ ⟨ ! e ⟩ ↗ a ⟧
  a₁ = α e p φ g (a₀ , a₀ExtendsG)

  p' : ⟦ p' ∈ Π (A ∘ p) ∣ ((φ , g) ↗ p') & (p' ⟨ e ⟩ ≈ a₀) ⟧
  p' = fill {A = A} e α p φ g a₀ a₀ExtendsG

  q : Int → (Σ x ∈ Int , A x)
  q i = (p i , fst p' i)

  h : [ φ ] → Π (B ∘ q)
  h u i = 
    let p'ExtendsG = fst (snd p') u in
    let atI = cong (λ f → f i) p'ExtendsG in
    subst (λ a → B (p i , a)) atI (snd (f u i))

  
  transLift :
    {i : Int}
    {Bᵢ : A (p i) → Set}
    {x y z : A (p i)}
    (q : y ≡ z)
    (p : x ≡ y)
    (r : x ≡ z)
    {bx : Bᵢ x}
    {by : Bᵢ y}
    (s : subst Bᵢ p bx ≡ by)
    → ---------
    subst Bᵢ r bx ≡ subst Bᵢ q by
  transLift refl refl refl refl = refl

  b₁ : ⟦ b ∈ (B ∘ q) ⟨ ! e ⟩ ∣ (φ , h) ∙ ⟨ ! e ⟩ ↗ b ⟧
  b₁ =
    β e q φ h (b₀' , wip) where
      b₀' : (B ∘ q) ⟨ e ⟩
      b₀' = subst (λ a → B (p ⟨ e ⟩ , a)) (symm (snd (snd p'))) b₀

      wip : prf ((φ , h) ∙ ⟨ e ⟩ ↗ b₀')
      wip u = transLift y≡z x≡y x≡z lhs≡rhs where
        -- The fibers over B (p ⟨ e ⟩, _)
        B₀ : A (p ⟨ e ⟩) → Set
        B₀ a = B (p ⟨ e ⟩ , a)

        -- We have 3 (propositionally) equal terms of type A (p ⟨ e ⟩)
        x y z : A (p ⟨ e ⟩)
        x = fst (f u ⟨ e ⟩); y = a₀; z = fst p' ⟨ e ⟩
        
        x≡y : x ≡ y
        x≡y = Σeq₁ (extendsF u)
        
        y≡z : y ≡ z
        y≡z = symm (snd (snd p'))
        
        x≡z : x ≡ z
        x≡z = cong (λ f → f ⟨ e ⟩) (fst (snd p') u)

        -- We want to show lhs = rhs in B₀ z      
        lhs : B₀ x
        lhs = snd (f u ⟨ e ⟩)

        rhs : B₀ y
        rhs = b₀

        -- First, show that they're equal in B₀ y        
        lhs≡rhs : subst B₀ x≡y lhs ≡ rhs
        lhs≡rhs = Σeq₂ (extendsF u)

  p'I≡a₁ : fst p' ⟨ ! e ⟩ ≡ fst a₁
  p'I≡a₁ = fillAtEnd {A = A} e α p φ g a₀ a₀ExtendsG

  b₁' : B (p ⟨ ! e ⟩ , fst a₁)
  b₁' = subst (λ a → B (p ⟨ ! e ⟩ , a)) p'I≡a₁ (fst b₁)

  extendsAt1 : prf ((φ , f) ∙ ⟨ ! e ⟩ ↗ (fst a₁ , b₁'))
  extendsAt1 u = Σext gI≡a₁ (transLift p'I≡a₁ gI≡p'I  gI≡a₁ (snd b₁ u)) where
    gI≡a₁ : g u ⟨ ! e ⟩ ≡ fst a₁
    gI≡a₁ = snd a₁ u

    gI≡p'I : g u ⟨ ! e ⟩ ≡ fst p' ⟨ ! e ⟩
    gI≡p'I = cong (λ f → f ⟨ ! e ⟩) (fst (snd p') u)

  
 fstFibΣid :
  {A : Int → Set}
  {B : (Σ x ∈ Int , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  (e : OI)(p : Int → Int)
  (φ : Cof)(f : [ φ ] → Π ((Σ' A B) ∘ p))
  (ab₀ : ⟦ ab ∈ Σ' A B (p ⟨ e ⟩) ∣ (φ , f) ∙ ⟨ e ⟩ ↗ ab ⟧)
  → -----------
  fst (fst (FibΣid {A} {B} α β e p φ f ab₀)) ≡ fst (α e p φ (λ u i → fst (f u i)) ((fst (fst ab₀)) , (λ u → cong fst (snd ab₀ u))))
 fstFibΣid α β e p φ f ab₀ = refl

_×id : {A A' : Set}{B : A' → Set}(f : A → A') → Σ A (B ∘ f) → Σ A' B
(f ×id) (a , b) = (f a , b)

FibΣ :
  {Γ : Set}
  {A : Γ → Set}
  {B : (Σ x ∈ Γ , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Σ' A B)
FibΣ {Γ} {A} {B} α β e p = FibΣid (reindex A α p) (reindex B β (p ×id)) e id

FibΣ' :
  {Γ : Set}
  (A : Fib Γ)
  (B : Fib (Σ x ∈ Γ , fst A x))
  → -----------
  Fib Γ
FibΣ' (A , α) (B , β) = Σ' A B , FibΣ {A = A} {B = B} α β

----------------------------------------------------------------------
-- Forming Σ-types is stable under reindexing
----------------------------------------------------------------------
reindexΣ :
  {Δ Γ : Set}
  (A : Γ → Set)
  (B : Σ Γ A → Set)
  (α : isFib A)
  (β : isFib B)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Σ' A B) (FibΣ {B = B} α β) ρ ≡ FibΣ {B = B ∘ (ρ ×id)} (reindex A α ρ) (reindex B β (ρ ×id))
reindexΣ A B α β ρ = refl
