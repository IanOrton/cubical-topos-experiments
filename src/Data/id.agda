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
module Data.id where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.paths
open import Data.products

----------------------------------------------------------------------
-- Id types
----------------------------------------------------------------------
Id : {Γ : Set}(A : Γ → Set) → Σ x ∈ Γ , A x × A x → Set
Id {Γ} A = Σ' (Path A) Prf where
  Prf : Σ (Σ Γ (λ x → A x × A x)) (Path A) → Set
  Prf ((x , (a , a')) , p) = ⟦ φ ∈ Cof ∣ fst φ ⊃ (All i ∈ Int , fst p i ≈ a) ⟧

pathToId : {Γ : Set}{A : Γ → Set}{x : Γ}{a a' : A x} → Path A (x , a' , a') → Id A (x , a' , a')
pathToId p = (p , cofFalse , (λ ()))

IdExt :
  {Γ : Set}
  {A : Γ → Set}
  {x : Γ}
  {a a' : A x}
  {id id' : Id A (x , (a , a'))}
  → ------------
  (fst (fst id) ≡ fst (fst id')) → (fst (fst (snd id))) ≡ fst (fst (snd id')) → id ≡ id'
IdExt {Γ} {A} {x} {a} {a'} {(p , u)} refl refl =
  let pathEq = (PathExt refl) in Σext pathEq (PrfExt pathEq refl) where
    Prf : Σ (Σ Γ (λ x → A x × A x)) (Path A) → Set
    Prf ((x , (a , a')) , p) = ⟦ φ ∈ Cof ∣ fst φ ⊃ (All i ∈ Int , fst p i ≈ a) ⟧
    PrfExt : {p p' : a ~ a'}(eq : p ≡ p'){u : Prf ((x , (a , a')) , p)}{v : Prf ((x , (a , a')) , p')}
      → fst (fst u) ≡ fst (fst v) → subst ((λ p → Prf ((x , a , a') , p))) eq u ≡ v
    PrfExt {p} {_} refl {((φ , _) , _)} refl =
      Σext (Σext refl (eq (cof φ))) (eq (φ ⊃ all Int (λ i → fst p i ≈ a)))

existsCof : (φ : Cof)(f : [ φ ]  → Ω) → ((u : [ φ ]) → prf (cof (f u))) → prf (cof (exists [ φ ] f))
existsCof φ f fCof = subst (prf ∘ cof) eqProps' cofφ&exists where
  imp : prf (fst φ ⊃ cof (exists [ φ ] f))
  imp u = subst (prf ∘ cof) eqProps (fCof u) where
    eqProps : f u ≡ exists [ φ ] f
    eqProps = propext (λ v → ∣ (u , v) ∣) (λ v → ∥∥-elim body (λ _ _ → eq (f u)) v) where
      body : Σ (prf (fst φ)) (λ v₁ → prf (f v₁)) → prf (f u)
      body (u' , fu') = subst (prf ∘ f) (eq (fst φ)) fu'
      
  eqProps' : (fst φ & exists [ φ ] f) ≡ exists [ φ ] f
  eqProps' = propext snd (λ u → (∥∥-rec (fst φ) fst u , u))
  
  cofφ&exists : prf (cof (fst φ & exists [ φ ] f))
  cofφ&exists = cof& (fst φ) (exists [ φ ] f) (snd φ) imp
  

FibId : {Γ : Set}{A : Γ → Set} → isFib A → isFib (Id A)
FibId {Γ} {A} α = FibΣ {B = Prf} (FibPath {A = A} α) β where
  Γ' : Set
  Γ' = Σ (Σ Γ (λ x → A x × A x)) (Path A)
  
  Prf : Γ' → Set
  Prf ((x , (a , a')) , p) = ⟦ φ ∈ Cof ∣ fst φ ⊃ (All i ∈ Int , fst p i ≈ a) ⟧
  
  prfExt : {x : Γ}{a a' : A x}{p : a ~ a'}{pr pr' : Prf ((x , (a , a')) , p)} → fst (fst pr) ≡ fst (fst pr') → pr ≡ pr'
  prfExt {x} {a} {a'} {p} {((φ , _) , _)} {_} refl = Σext (Σext refl (eq (cof φ))) (eq (φ ⊃ (All i ∈ Int , fst p i ≈ a)))
  
  β : isFib Prf
  β e p φ f φ' = ψ where
    ψ : ⟦ ψ ∈ (Prf (p ⟨ ! e ⟩)) ∣ (φ , f) ∙ ⟨ ! e ⟩ ↗ ψ ⟧
    fst (fst ψ) = (exists [ φ ] fI , existsCof φ fI (λ u → snd (fst (f u ⟨ ! e ⟩)))) where
      fI : [ φ ] → Ω
      fI u = fst (fst (f u ⟨ ! e ⟩))
    snd (fst ψ) ex i = ex goal proof where
      goal : Ω
      goal = fst (snd (p ⟨ ! e ⟩)) i ≈ fst (snd (fst (p ⟨ ! e ⟩)))
      proof : Σ [ φ ] (λ u → prf (fst (fst (f u ⟨ ! e ⟩)))) → prf (goal)
      proof (u , v) = snd (f u ⟨ ! e ⟩) v i
    snd ψ u = prfExt {p = snd (p ⟨ ! e ⟩)} (propext (λ v → ∣ u , v ∣) backwards) where
      backwards : prf (fst (fst (fst ψ))) → prf (fst (fst (f u ⟨ ! e ⟩)))
      backwards v = ∥∥-rec (fst (fst (f u ⟨ ! e ⟩))) (λ pair → subst (λ v → [ fst (f v ⟨ ! e ⟩) ]) (eq (fst φ )) (snd pair)) v


reflId : {Γ : Set}(A : Γ → Set){x : Γ}(a : A x) → Id A (x , (a , a))
reflId {Γ} A {x} a = (reflPath {A = A} a , (cofTrue , (λ tt i → refl)))


private
 triple :
  {Γ : Set}
  (A : Γ → Set)
  {x : Γ}
  {a : A x}
  (B : Σ a' ∈ (A x) , Id A (x , (a , a')) → Set)
  (a' : A x)
  (e : Id A (x , (a , a')))
  (b : B (a' , e))
  → Σ a' ∈ (A x) , Σ e ∈ (Id A (x , (a , a'))) , B (a' , e)
 triple _ _ a' e b = (a' , e , b)

private
 tripleExt :
  {Γ : Set}
  (A : Γ → Set)
  {x : Γ}
  {a₀ : A x}
  (B : Σ a' ∈ (A x) , Id A (x , (a₀ , a')) → Set)
  {a a' : A x}
  {e  : Id A (x , (a₀ , a))}
  {e' : Id A (x , (a₀ , a'))}
  {b  : B (a , e)}
  {b' : B (a' , e')}
  (_ : a ≡ a')
  (_ : fst (fst e) ≡ fst (fst e'))
  (_ : fst (fst (snd e)) ≡  fst (fst (snd e')))
  (eqB : (p : (a , e) ≡ (a' , e')) → subst B p b ≡ b')
  -----------------
  → triple A B a e b ≡ triple A B a' e' b'
 tripleExt A {x} {a₀} B {a} .{a} {e} {e'} {b} {b'} refl p q eqB =
   Σext refl (Σext (IdExt {A = A} p q) (trans step₂ step₁)) where
     substLemma : (e' : Id A (x , (a₀ , a)))(p : e ≡ e')
       → subst (λ e → B (a , e)) p b ≡ subst B (Σext refl p) b
     substLemma _ refl = refl
     step₁ : subst (λ e₁ → B (a , e₁)) (IdExt {A = A} p q) b ≡ subst B (Σext refl (IdExt {A = A} p q)) b
     step₁ = substLemma e' (IdExt {A = A} p q)
     step₂ : subst B (Σext refl (IdExt {A = A} p q)) b ≡ b'
     step₂ = eqB ((Σext refl (IdExt {A = A} p q)))

private
 Jinternal :
  {Γ : Set}
  {A : Γ → Set}
  {x : Γ}
  {a : A x}
  (B : Σ a' ∈ (A x) , Id A (x , (a , a')) → Set)
  (β : isFib B)
  (a' : A x)
  (e : Id A (x , (a , a')))
  → -------------
  (b : B (a , reflId A a)) → ⟦ b' ∈ B(a' , e) ∣ fst (fst (snd e)) ⊃ (triple A B a' e b') ≈ (triple A B a (reflId A a) b) ⟧
 Jinternal {Γ} {A} {x} {a} B β a' (p , φ , pRefl) b = (bI' , atRefl) where
  q : (i : Int) → Id A (x , (a , fst p i))
  fst (fst (q i)) j = fst p (min i j)
  fst (snd (fst (q i))) = fst (snd p)
  snd (snd (fst (q i))) = refl
  fst (snd (q i)) = φ ∨ i ≈O
  snd (snd (q i)) u j = or-elim-eq (λ _ → fst p (min i j)) a (λ {l} → pRefl l (min i j)) (λ {r} → right i r) u where
    right : (i : Int) → (i ≡ O) → fst p (min i j) ≡ a
    right .O refl = fst (snd p)

  substEq : {x : Γ}{a a' : A x}(equal : a ≡ a')(goal : Id A (x , (a , a')))
    → fst (fst (reflId A a)) ≡ fst (fst goal)
    → [ fst (snd goal) ]
    → subst (λ a'' → Id A (x , a , a'')) equal (reflId A a) ≡ goal
  substEq refl goal equal u = IdExt {A = A} equal (propext (λ _ → u) (λ _ → tt))

  coePath : (i : Int)(equal : (j : Int) → a ≡ fst p (min i j))(u : [ φ ∨ i ≈O ])
    → (a , reflId A a) ≡ (fst p i , q i)
  coePath i equal u = Σext (equal I) (substEq (equal I) (q i) (funext equal) u)

  coeB : (i : Int)(equal : (j : Int) → a ≡ fst p (min i j))(u : [ φ ∨ i ≈O ])
    → B (a , reflId A a) → B (fst p i , q i)
  coeB i equal u b = subst B (coePath i equal u) b
    
  f : [ φ ] → Π (B ∘ (λ i → fst p i , q i))
  f u i = coeB i (λ j → symm (pRefl u (min i j))) ∣ inl u ∣ b
    
  b' : B (fst p O , q O)
  b' = coeB O (λ _ → a≡pO) ∣ inr refl ∣ b where
    a≡pO : a ≡ fst p O
    a≡pO = symm (fst (snd p))
    
  congSubst : {A : Set}{a a' : A}(B : A → Set)(p q : a ≡ a')(b b' : B a) → b ≡ b' → subst B p b ≡ subst B q b'
  congSubst B refl refl b .b refl = refl

  extends : prf ((φ , f) ∙ O ↗ b')
  extends u = congSubst B eq₁ eq₂ b b refl where
    eq₁ : (a , reflId A a) ≡ (fst p O , q O)
    eq₁ = coePath O (λ j → symm (pRefl u O)) ∣ inl u ∣
    eq₂ : (a , reflId A a) ≡ (fst p O , q O)
    eq₂ = coePath O (λ _ → symm (fst (snd p))) ∣ inr refl ∣

  bI : B (fst p I , q I)
  bI = fst (β O' (λ i → (fst p i , q i)) φ f (b' , extends))

  pI≡a : fst p I ≡ a'
  pI≡a = snd (snd p)

  substEq' : {a' a'' : A x}(equal : a' ≡ a'')(id : Id A (x , (a , a')))(id' : Id A (x , (a , a'')))
    → fst (fst id) ≡ fst (fst id')
    → fst (fst (snd id)) ≡ fst (fst (snd id'))
    → subst (λ a'' → Id A (x , a , a'')) equal id ≡ id'
  substEq' refl id id' eq₁ eq₂  = IdExt {A = A} eq₁ eq₂

  qI≡p : subst (λ a' → Id A (x , (a , a'))) pI≡a (q I) ≡ (p , φ , pRefl)
  qI≡p = substEq' pI≡a (q I) (p , φ , pRefl) refl eqProps where
    eqProps : fst (φ ∨ I ≈O) ≡ fst φ
    eqProps = propext
      (λ u → u (fst φ) (λ{ (inl u) → u ; (inr I≡O) → ∅-elim (O≠I (symm I≡O)) }))
      (λ u → ∣ inl u ∣)

  bI' : B (a' , p , φ , pRefl)
  bI' = subst B (Σext pI≡a qI≡p) bI

  fI≡bI : (u : [ φ ]) → f u I ≡ bI
  fI≡bI u = snd (β O' (λ i → (fst p i , q i)) φ f (b' , extends)) u 
    
  substSwap : {A : Set}{a a' : A}(B : A → Set)(p : a ≡ a')(q : a' ≡ a)(b : B a)(b' : B a') → subst B p b ≡ b' → b ≡ subst B q b'
  substSwap B refl refl b .b refl = refl
    
  substTrans : {A : Set}{a a' a'' : A}(B : A → Set)(p : a ≡ a')(q : a' ≡ a'')(b : B a) → subst B (trans q p) b ≡ subst B q (subst B p b)
  substTrans B refl refl b = refl

  b≡bI' : (u : [ φ ])(equal : (a' , p , φ , pRefl) ≡ (a , reflId A a)) → subst B equal bI' ≡ b
  b≡bI' u equal = let rr = symm (trans sbI≡sbI' b≡sbI) in rr where
    b≡sbI : b ≡ subst B (trans equal (Σext pI≡a qI≡p)) bI
    b≡sbI = substSwap B (coePath I (λ j → symm (pRefl u j)) ∣ inl u ∣) (trans equal (Σext pI≡a qI≡p)) b bI (fI≡bI u)
    sbI≡sbI' : subst B (trans equal (Σext pI≡a qI≡p)) bI ≡ subst B equal bI'
    sbI≡sbI' = substTrans B (Σext pI≡a qI≡p) equal bI

  atRefl : (u : [ φ ]) → (triple A B a' (p , φ , pRefl) bI') ≡ (triple A B a (reflId A a) b)
  atRefl u = tripleExt A B (trans (pRefl u I) (symm (snd (snd p)))) (funext (pRefl u)) (propext (λ _ → tt) (λ _ → u)) (b≡bI' u)


J :
  {Γ : Set}
  {A : Γ → Set}
  {x : Γ}
  {a : A x}
  (B : Σ a' ∈ (A x) , Id A (x , (a , a')) → Set)
  (β : isFib B)
  (a' : A x)
  (e : Id A (x , (a , a')))
  → -------------
  B (a , reflId A a) → B(a' , e)
J {Γ} {A} {x} {a} B β a' e b = fst (Jinternal {A = A} B β a' e b)


Jrefl :
  {Γ : Set}
  {A : Γ → Set}
  {x : Γ}
  {a : A x}
  (B : Σ a' ∈ (A x) , Id A (x , (a , a')) → Set)
  (β : isFib B)
  (b : B (a , reflId A a))
  → -------------
  J {A = A} B β a (reflId A a) b ≡ b
Jrefl {Γ} {A} {x} {a} B β b = extractEq (snd (Jinternal {A = A} B β a (reflId A a) b) tt) where
  extractEq :
    {b b' : B (a , reflId A a)}
    → -------------
    triple A B a (reflId A a) b ≡ triple A B a (reflId A a) b' → b ≡ b' 
  extractEq {b} .{b} refl = refl
