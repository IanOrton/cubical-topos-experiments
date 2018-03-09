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
module Data.paths where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.products

----------------------------------------------------------------------
-- Path types
----------------------------------------------------------------------
_~~_ : {A : Int → Set}(a : A O)(a' : A I) → Set
_~~_ {A} a a' = ⟦ p ∈ (Π A) ∣ (p O ≈ a) & (p I ≈ a') ⟧

_at_ : {A : Int → Set}{a : A O}{a' : A I}(p : a ~~ a')(i : Int) → A i
(p , _) at i = p i

atO : {A : Int → Set}{a : A O}{a' : A I}(p : _~~_ {A} a a') → p at O ≡ a
atO p = fst (snd p)

atI : {A : Int → Set}{a : A O}{a' : A I}(p : _~~_ {A} a a') → p at I ≡ a'
atI p = snd (snd p)

_~_ : {A : Set}(a a' : A) → Set
_~_ {A} a a' = _~~_ {A = λ _ → A} a a'

transDep : {A : Int → Set}{α : isFib A}{a a' : A O}{b : A I} → (a ~~ b) → (a' ~~ b) → (a ~ a')
transDep {A} {α} {a} {a'} {b} (p , pO , pI) (q , qO , qI) = ((λ i → fst (r i)) , rO≡a , rI≡a') where
  f : (i : Int) → [ i ≈O ∨ i ≈I ] → Π A
  f i u j = OI-elim cases u where
    cases : (i ≡ O) ⊎ (i ≡ I) → A j
    cases (inl _) = p j
    cases (inr _) = q j
    
  r : (i : Int) → ⟦ a ∈ (A O) ∣ ((i ≈O ∨ i ≈I) , f i) ∙ O ↗ a ⟧
  r i = α I' id (i ≈O ∨ i ≈I) (f i) (b , or-elim-eq (λ u → f i u I) b pI qI)

  rO≡a : fst (r O) ≡ a
  rO≡a = trans pO (symm (snd (r O) ∣ inl refl ∣))

  rI≡a' : fst (r I) ≡ a'
  rI≡a' = trans qO (symm (snd (r I) ∣ inr refl ∣))

transDep' : {A : Int → Set}{α : isFib A}{a : A O}{b b' : A I} → (a ~~ b) → (a ~~ b') → (b ~ b')
transDep' {A} {α} {a} {b} {b'} (p , pO , pI) (q , qO , qI) = ((λ i → fst (r i)) , rO≡a , rI≡a') where
  f : (i : Int) → [ i ≈O ∨ i ≈I ] → Π A
  f i u j = OI-elim cases u where
    cases : (i ≡ O) ⊎ (i ≡ I) → A j
    cases (inl _) = p j
    cases (inr _) = q j
    
  r : (i : Int) → ⟦ b ∈ (A I) ∣ ((i ≈O ∨ i ≈I) , f i) ∙ I ↗ b ⟧
  r i = α O' id (i ≈O ∨ i ≈I) (f i) (a , or-elim-eq (λ u → f i u O) a pO qO)

  rO≡a : fst (r O) ≡ b
  rO≡a = trans pI (symm (snd (r O) ∣ inl refl ∣))

  rI≡a' : fst (r I) ≡ b'
  rI≡a' = trans qI (symm (snd (r I) ∣ inr refl ∣))

transPath : {A : Set}(α : isFib {Γ = Unit} (λ _ → A)){x y z : A} → x ~ y → y ~ z → x ~ z
transPath {A} α {x} {y} {z} p q = ((λ i → fst (r i)) , rO≡x , rI≡z) where
  f : (i : Int) → [ i ≈O ∨ i ≈I ] → Π (λ _ → A)
  f i u j = OI-elim cases u where
    cases : (i ≡ O) ⊎ (i ≡ I) → A
    cases (inl _) = x 
    cases (inr _) = fst q j
  
  qO=pI : (i : Int)(eq : i ≡ I) → fst q O ≡ fst p i
  qO=pI .I refl = trans (symm (snd (snd p))) (fst (snd q))

  pO=pi : (i : Int)(l : i ≡ O) → fst p O ≡ fst p i
  pO=pi .O refl = refl
  
  r : (i : Int) → ⟦ a ∈ A ∣ ((i ≈O ∨ i ≈I) , f i) ∙ I ↗ a ⟧
  r i = α O' (λ _ → tt) (i ≈O ∨ i ≈I) (f i)
    ((fst p i , or-elim-eq (λ u → f i u O) (fst p i) (λ {l} → trans (pO=pi i l) (symm (fst (snd p)))) (λ {r} → qO=pI i r)))

  rO≡x : fst (r O) ≡ x
  rO≡x = symm (snd (r O) ∣ inl refl ∣)

  rI≡z : fst (r I) ≡ z
  rI≡z = trans (snd (snd q)) (symm (snd (r I) ∣ inr refl ∣))

congPath :
  {A : Set}
  {B : Set}
  (f : A → B)
  {x y : A}
  (p : x ~ y)
  → -----------
  f x ~ f y
congPath f p = ((f ∘ (fst p)) , (cong f (fst (snd p))) , cong f (snd (snd p)))

fillPath : {P : Int → Set}(ρ : isFib P)(x : P O) → _~~_ {P} x (fst (ρ O' id cofFalse ∅-elim (x , λ ())))
fillPath ρ x =
  let filler = fill O' ρ id cofFalse ∅-elim x (λ ()) in
  fst filler , snd (snd filler) , fillAtEnd O' ρ id cofFalse ∅-elim x (λ ())

fillPath' : {P : Int → Set}(ρ : isFib P)(x : P I) → _~~_ {P} (fst (ρ I' id cofFalse ∅-elim (x , λ ()))) x
fillPath' ρ x =
  let filler = fill I' ρ id cofFalse ∅-elim x (λ ()) in
  fst filler , fillAtEnd I' ρ id cofFalse ∅-elim x (λ ()) , snd (snd filler)


Path : {Γ : Set}(A : Γ → Set) → Σ x ∈ Γ , A x × A x → Set
Path A (x , (a , a')) = a ~ a'

reflPath : {Γ : Set}{A : Γ → Set}{x : Γ}(a : A x) → Path A (x , (a , a))
reflPath a = ((λ _ → a) , refl , refl)

reflPath' : {A : Set}{a a' : A} → (a ≡ a') → a ~ a'
reflPath' {A} {a} .{a} refl = ((λ _ → a) , (refl , refl))

reflPathEval : {A : Set}{a a' : A}(p : a ≡ a')(i : Int) → fst (reflPath' p) i ≡ a'
reflPathEval refl i = refl

PathExt : {A : Set}{a a' : A}{p q : a ~ a'} → fst p ≡ fst q → p ≡ q
PathExt refl = Σext refl (Σext uipImp uipImp)

abstract
 FibPathId :
  {A : Int → Set}
  (α : isFib A)
  → -----------
  isFib (Path A)
 FibPathId {A} α e p φ f path₀ = (path₁ , fExtends) where
  f' : Int → [ φ ] → Π (A ∘ fst ∘ p)
  f' i u j = fst (f u j) i
  
  f₀ : (i : Int) → ⟦ g ∈ ([ i ≈O ] → Π (A ∘ fst ∘ p)) ∣ (φ , f' i) ⌣ (i ≈O , g) ⟧
  fst (f₀ i) _ j = fst (snd (p j))
  snd (f₀ .O) u refl = funext (λ j → fst (snd (f u j)))
  
  f₀' : (i : Int) → [ φ ∨ i ≈O ] → Π (A ∘ fst ∘ p)
  f₀' i = _∪_ {φ = φ} {ψ = i ≈O} (f' i) (fst (f₀ i)) {p = snd (f₀ i)}
  
  f₁ : (i : Int) → ⟦ g ∈ ([ i ≈I ] → Π (A ∘ fst ∘ p)) ∣ ((φ ∨ i ≈O) , f₀' i)  ⌣ (i ≈I , g) ⟧
  fst (f₁ i) _ j = snd (snd (p j))
  snd (f₁ .I) u refl = funext (λ j →
    or-elim-eq (λ v → f₀' I v j) (snd (snd (p j))) (λ {u'} → snd (snd (f u' j))) (λ {I≡O} → ∅-elim (O≠I (symm I≡O))) u)
    
  f₁' : (i : Int) → [ (φ ∨ i ≈O) ∨ i ≈I ] → Π (A ∘ fst ∘ p)
  f₁' i = _∪_ {φ = φ ∨ i ≈O} {ψ = i ≈I} (f₀' i) (fst (f₁ i)) {p = snd (f₁ i)}
  
  extends : (i : Int) → prf ((((φ ∨ i ≈O) ∨ i ≈I) , f₁' i) ∙ ⟨ e ⟩ ↗ fst (fst path₀) i)
  extends i u = or-elim-eq (λ v → f₁' i v ⟨ e ⟩) (fst (fst path₀) i) (λ {l} → leftCase l) (λ {r} → rightCase i r) u where
    rightCase : (i : Int)(r : i ≡ I) → f₁' i ∣ inr r ∣ ⟨ e ⟩ ≡ fst (fst path₀) i
    rightCase .I refl = symm (snd (snd (fst path₀)))
    leftCase : (l : prf (fst (φ ∨ i ≈O))) → f₁' i ∣ inl l ∣ ⟨ e ⟩ ≡ fst (fst path₀) i
    leftCase l = or-elim-eq (λ v → f₁' i ∣ inl v ∣ ⟨ e ⟩) (fst (fst path₀) i) (λ {l} → llCase l) (λ {r} → rlCase i r) l where
      rlCase : (i : Int)(r : i ≡ O) → f₁' i ∣ inl ∣ inr r ∣ ∣ ⟨ e ⟩ ≡ fst (fst path₀) i
      rlCase .O refl = symm (fst (snd (fst path₀)))
      llCase : (l : [ φ ]) → f₁' i ∣ inl ∣ inl l ∣ ∣ ⟨ e ⟩ ≡ fst (fst path₀) i
      llCase u = cong (λ p → fst p i) (snd path₀ u)
      
  comp : (i : Int) → ⟦ a ∈ ((A ∘ fst ∘ p) ⟨ ! e ⟩) ∣ (((φ ∨ i ≈O) ∨ i ≈I) , f₁' i) ∙ ⟨ ! e ⟩ ↗ a ⟧
  comp i = α e (fst ∘ p) ((φ ∨ i ≈O) ∨ i ≈I) (f₁' i) (fst (fst path₀) i , extends i)
  
  path₁ : (Path A ∘ p) ⟨ ! e ⟩
  fst path₁ i = fst (comp i)
  fst (snd path₁) = symm eqAtO where
    eqAtO : fst (snd (p ⟨ ! e ⟩)) ≡ fst (comp O)
    eqAtO = snd (comp O) ∣ inl ∣ inr refl ∣ ∣
  snd (snd path₁) = symm eqAtI where
    eqAtI : snd (snd (p ⟨ ! e ⟩)) ≡ fst (comp I)
    eqAtI = snd (comp I) ∣ inr refl ∣

  fExtends : prf ((φ , f) ∙ ⟨ ! e ⟩ ↗ path₁)
  fExtends u = PathExt (funext (λ i → snd (comp i) ∣ inl ∣ inl u ∣ ∣))

FibPath :
  {Γ : Set}
  {A : Γ → Set}
  (α : isFib A)
  → -----------
  isFib (Path A)
FibPath {Γ} {A} α e p = FibPathId (reindex A α (fst ∘ p)) e (id× p) where
  id×_ : (p : Int → Σ Γ (λ x → A x × A x)) → Int → Σ Int (λ i → A (fst (p i)) × A (fst (p i)))
  (id× p) i = (i , snd (p i))

FibPath' :
  {Γ : Set}
  (A : Fib Γ)
  → -----------
  Fib (Σ x ∈ Γ , fst A x × fst A x)
FibPath' (A , α) = (Path A , FibPath {A = A} α)

funextPath : {A : Set}{B : A → Set}{f g : (x : A) → B x} → ((a : A) → f a ~ g a) → f ~ g
fst (funextPath pointwise) i a = fst (pointwise a) i
fst (snd (funextPath pointwise)) = funext (λ a → fst (snd (pointwise a)))
snd (snd (funextPath pointwise)) = funext (λ a → snd (snd (pointwise a)))

----------------------------------------------------------------------
-- Forming Path types is stable under reindexing
----------------------------------------------------------------------
reindexPath :
  {Δ Γ : Set}
  (A : Γ → Set)
  (α : isFib A)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Path A) (FibPath α) (ρ ×id) ≡ FibPath (reindex A α ρ)
reindexPath A α ρ = refl
