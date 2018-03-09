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
module fibrations where 

open import prelude
open import impredicative
open import interval
open import cof

----------------------------------------------------------------------
-- Path composition structure
----------------------------------------------------------------------
Comp : OI → (Int → Set) → Set
Comp e A = (φ : Cof)(f : [ φ ] → Π A) →
  ⟦ x₁ ∈ (A ⟨ e ⟩) ∣ (φ , f) ∙ ⟨ e ⟩ ↗ x₁ ⟧ →
  ⟦ x₀ ∈ (A ⟨ ! e ⟩) ∣ (φ , f) ∙ ⟨ ! e ⟩ ↗ x₀ ⟧

----------------------------------------------------------------------
-- Fibrations
----------------------------------------------------------------------
isFib : ∀{a}{Γ : Set a}(A : Γ → Set) → Set a
isFib {Γ = Γ} A = (e : OI)(p : Int → Γ) → Comp e (A ∘ p)

Fib : ∀{a}(Γ : Set a) → Set (lsuc lzero ⊔ a)
Fib {a} Γ = Σ (Γ → Set) isFib

----------------------------------------------------------------------
-- Fibrations can be reindexed
----------------------------------------------------------------------
reindex : ∀{a a'}{Δ : Set a}{Γ : Set a'}(A : Γ → Set)(α : isFib A)(ρ : Δ → Γ) → isFib (A ∘ ρ)
reindex A α ρ e p = α e (ρ ∘ p)

reindex' : ∀{a a'}{Δ : Set a}{Γ : Set a'}(Aα : Fib Γ)(ρ : Δ → Γ) → Fib Δ
reindex' (A , α) ρ = (A ∘ ρ , reindex A α ρ)

----------------------------------------------------------------------
-- Reindexing is functorial
----------------------------------------------------------------------
reindexId : {Γ : Set}{A : Γ → Set}{α : isFib A} → α ≡ reindex A α id 
reindexId = refl

reindexComp :
  {Γ₁ Γ₂ Γ₃ : Set}{A : Γ₃ → Set}{α : isFib A}
  (f : Γ₁ → Γ₂)(g : Γ₂ → Γ₃)
  → ----------------------
  reindex A α (g ∘ f) ≡ reindex (A ∘ g) (reindex A α g) f
reindexComp g f = refl

reindexId' : {Γ : Set}{A : Fib Γ} → reindex' A id ≡ A
reindexId' = refl

abstract
 reindexComp' :
  {Γ₁ Γ₂ Γ₃ : Set}{A : Fib Γ₃}
  (f : Γ₁ → Γ₂)(g : Γ₂ → Γ₃)
  → ----------------------
  reindex' A (g ∘ f) ≡ reindex' (reindex' A g) f
 reindexComp' g f = refl


----------------------------------------------------------------------
-- Using the fibration structure to interpret Γ ⊢ comp^i A [φ ↦ u] a₀
----------------------------------------------------------------------
comp^i :
  -- Context Γ
  {Γ : Set}
  -- Fibrant type Γ, i:𝕀 ⊢ A
  (A : (Γ × Int) → Set)
  (α : isFib A)
  -- Face formula Γ ⊢ φ : 𝔽
  (φ : Γ → Cof)
  -- Partial element Γ, φ, i:𝕀 ⊢ u : A
  (u : (x : Γ)(_ : [ φ x ])(i : Int) → A (x , i))
  -- Term Γ ⊢ a₀ : A(i0)[φ ↦ u(i0)]
  (a₀ : ⟦ a₀ ∈ ((x : Γ) → A (x , O)) ∣ All x ∈ Γ , ((φ x , u x) ∙ O ↗ a₀ x) ⟧)
  → -------------
  -- Resulting term:  Γ ⊢ comp^i A [φ ↦ u] a₀
  ⟦ a₁ ∈ ((x : Γ) → A (x , I)) ∣ All x ∈ Γ , ((φ x , u x) ∙ I ↗ a₁ x) ⟧
comp^i A α φ u (a₀ , ext) =
  ( (λ x → fst (α O' (λ i → x , i) (φ x) (u x) (a₀ x , ext x)))
  , (λ x → snd (α O' (λ i → x , i) (φ x) (u x) (a₀ x , ext x))) )

-- This has the required uniformity property
comp^iReindex :
  {Δ Γ : Set}
  (A : (Γ × Int) → Set)
  (α : isFib A)
  (φ : Γ → Cof)
  (u : (x : Γ)(_ : [ φ x ])(i : Int) → A (x , i))
  (a₀ : ⟦ a₀ ∈ ((x : Γ) → A (x , O)) ∣ All x ∈ Γ , ((φ x , u x) ∙ O ↗ a₀ x) ⟧)
  (f : Δ → Γ)
  → -------------
  (λ x → fst (comp^i A α φ u a₀) (f x))
      ≡ fst (comp^i (A ∘ (f ×' id)) (reindex A α (f ×' id)) (φ ∘ f)
          (λ x φfx → u (f x) φfx) ((λ x → fst a₀ (f x)) , (λ x → snd a₀ (f x))))
comp^iReindex A α φ u a₀ f = refl

----------------------------------------------------------------------
-- Trvial compositions might not reduce (we don't have regularity)
----------------------------------------------------------------------
trivComp : {Γ : Set}(A : Fib Γ)(e : OI)(x : Γ)(a : fst A x) → fst A x
trivComp (A , α) e x a = fst (α e (λ _ → x) cofFalse ∅-elim (a , (λ ())))

----------------------------------------------------------------------
-- An extentionality principle for fibration structures
----------------------------------------------------------------------
fibExt : {Γ : Set}{A : Γ → Set}{α α' : isFib A}
  → ((e : OI)(p : Int → Γ)
     (φ : Cof)(f : [ φ ] → Π (A ∘ p))
     (a₀ : ⟦ x₁ ∈ (A (p ⟨ e ⟩)) ∣ (φ , f) ∙ ⟨ e ⟩ ↗ x₁ ⟧) → fst (α e p φ f a₀) ≡ fst (α' e p φ f a₀))
  → α ≡ α'
fibExt {α = α} {α'} ext =
  funext (λ e → funext (λ p → funext (λ φ → funext (λ f →
    funext (λ a₀ → incMono (λ x → (φ , f) ∙ ⟨ ! e ⟩ ↗ x) (α e p φ f a₀) (α' e p φ f a₀) (ext e p φ f a₀))))))

----------------------------------------------------------------------
-- Terminal object is fibrant
----------------------------------------------------------------------
FibUnit : {Γ : Set} → isFib(λ(_ : Γ) → Unit)
fst (FibUnit _ _ _ _ (unit , _))   = unit
snd (FibUnit _ _ _ _ (unit , _)) _ = refl

----------------------------------------------------------------------
-- Initial object is fibrant
----------------------------------------------------------------------
Fib∅ : {Γ : Set} → isFib(λ(_ : Γ) → ∅)
Fib∅ _ _ _ _ (() , _)

----------------------------------------------------------------------
-- Fibrations are closed under isomorphism
----------------------------------------------------------------------
_≅_ : {Γ : Set}(A B : Γ → Set) → Set
_≅_ {Γ} A B = (x : Γ) → Σ f ∈ (A x → B x) , Σ g ∈ (B x → A x) , (g ∘ f ≡ id) × (f ∘ g ≡ id)

FibIso : {Γ : Set}(A B : Γ → Set) → (A ≅ B) → isFib A → isFib B
FibIso A B iso α e p φ q b = b' where
  !e : Int
  !e = ⟨ ! e ⟩
  f : (i : Int) → A (p i) → B (p i)
  f i = fst (iso (p i))
  g : (i : Int) → B (p i) → A (p i)
  g i = fst (snd (iso (p i)))
  q' : [ φ ] → Π (A ∘ p)
  q' u i = g i (q u i)
  a : ⟦ a ∈ ((A ∘ p) ⟨ e ⟩) ∣ ((φ , q') ∙ ⟨ e ⟩) ↗ a ⟧
  fst a = g ⟨ e ⟩ (fst b)
  snd a u = cong (g ⟨ e ⟩) (snd b u)
  a' : ⟦ a ∈ ((A ∘ p) !e) ∣ ((φ , q') ∙ !e) ↗ a ⟧
  a' = α e p φ q' a
  b' : ⟦ b ∈ ((B ∘ p) !e) ∣ ((φ , q) ∙ !e) ↗ b ⟧
  fst b' = f !e (fst a')
  snd b' u = z where
    x : q' u !e ≡ fst a'
    x = snd a' u
    y : f !e (q' u !e) ≡ f !e (fst a')
    y = cong (f !e) x
    z : q u !e ≡ f !e (fst a')
    z = trans y (cong (λ f → f (q u !e)) (symm (snd (snd (snd (iso (p !e)))))))

-- trans fgq≡b' (symm (fgq≡q)) where
--     fgq≡b' : f !e (g !e (q u !e)) ≡ fst b'
--     fgq≡b' = cong (f !e) (snd a' u)
--     fgq≡q : f !e (g !e (q u !e)) ≡ q u !e
--     fgq≡q = cong (λ f → f (q u !e)) (snd (snd (snd (iso (p !e)))))

trivialFibIso : {Γ : Set}(A B : Γ → Set)(iso : A ≅ B)(α : isFib A)
  (p : Int → Γ)(b : B (p O))
  → fst (FibIso A B iso α O' p cofFalse ∅-elim (b , λ ()))
    ≡ fst (iso (p I)) (fst (α O' p cofFalse ∅-elim (fst (snd (iso (p O))) b , λ ())))
trivialFibIso A B iso α p b =
  cong (λ hh' → fst (iso (p I)) (fst (α O' p cofFalse (fst hh') (fst (snd (iso (p O))) b , snd hh'))))
    (Σext (funext (λ ())) (funext (λ ())))
  
----------------------------------------------------------------------
-- Path filling structure
----------------------------------------------------------------------
Fill : OI → (Int → Set) → Set
Fill e A =
  (φ : Cof)
  (f : [ φ ] → Π A)
  (a : A ⟨ e ⟩)
  (_ : prf ((φ , f) ∙ ⟨ e ⟩ ↗ a))
  → --------------------------------------
  ⟦ p ∈ Π A ∣ ((φ , f ) ↗ p) & (p ⟨ e ⟩ ≈ a) ⟧

----------------------------------------------------------------------
-- Compatible partial functions
----------------------------------------------------------------------
_⌣_ : {A : Set} → □ A → □ A → Ω
(φ , f) ⌣ (ψ , g) = All u ∈ [ φ ] , All v ∈ [ ψ ] , f u ≈ g v

_∪_ :
  {A : Set}
  {φ ψ : Cof}
  (f : [ φ ] → A)
  (g : [ ψ ] → A)
  {p : prf((φ , f) ⌣ (ψ , g))}
  → ---------------------------
  [ φ ∨ ψ ] → A
_∪_ {A} {φ} {ψ} f g {p} w = ∥∥-elim h q w where

  h : [ φ ] ⊎ [ ψ ] → A
  h (inl u) = f u
  h (inr v) = g v

  q : (z z' : [ φ ] ⊎ [ ψ ]) → h z ≡ h z'
  q (inl _) (inl _) = cong f (eq (fst φ))
  q (inl u) (inr v) = p u v
  q (inr v) (inl u) = symm (p u v)
  q (inr _) (inr _) = cong g (eq (fst ψ))

----------------------------------------------------------------------
-- Path filling from path composition
----------------------------------------------------------------------
private
 fillInternal :
  {Γ : Set}
  {A : Γ → Set}
  (e : OI)
  (α : isFib A)
  (p : Int → Γ)
  (φ : Cof)
  (f : [ φ ] → Π (A ∘ p))
  (a : A (p ⟨ e ⟩))
  (u : prf ((φ , f) ∙ ⟨ e ⟩ ↗ a))
  → -----------
  Σ fill ∈ ⟦ p ∈ Π (A ∘ p) ∣ ((φ , f ) ↗ p) & (p ⟨ e ⟩ ≈ a) ⟧ , fst fill ⟨ ! e ⟩ ≡ fst (α e p φ f (a , u))
fillInternal {Γ} {A} e α p φ f a u = (result , fillAtOne) where
  p' : (i : Int) → Int → Γ
  p' i j = p (cnx e i j)

  f' : (i : Int) → [ φ ] → Π(A ∘ (p' i))
  f' i u j = f u (cnx e i j)

  g : (i : Int) → [ i ≈OI e ] → Π(A ∘ (p' i))
  g .(⟨ e ⟩) refl j = a

  agree : (i : Int) → prf ((φ , f' i) ⌣ (i ≈OI e , g i))
  agree .(⟨ e ⟩) v refl = funext (λ j → u v)

  h : (i : Int) → [ φ ∨ i ≈OI e ] → Π(A ∘ (p' i))
  h i = _∪_ {φ = φ} {ψ = i ≈OI e} (f' i) (g i) { p = agree i }

  AtZero : Int → Ω
  AtZero i = ((φ ∨ i ≈OI e) , h i) ∙ ⟨ e ⟩ ↗ a
  hAtZero : (i : Int) → prf (AtZero i)
  hAtZero i v = ∥∥-rec (AtZero i) (cases i) v v where
    cases : (i : Int) → prf (fst φ) ⊎ (i ≡ ⟨ e ⟩) → prf (AtZero i)
    cases i (inl x) v = -- φ holds
      proof:
        snd (((φ ∨ i ≈OI e) , h i) ∙ ⟨ e ⟩) v
          ≡[ cong (snd (((φ ∨ i ≈OI e) , h i) ∙ ⟨ e ⟩)) (equ ((fst φ or i ≈ ⟨ e ⟩)) v (∣ inl x ∣)) ]≡
        snd (((φ ∨ i ≈OI e) , h i) ∙ ⟨ e ⟩) (∣ inl x ∣)
          ≡[ refl ]≡
        f x ⟨ e ⟩
          ≡[ u x ]≡
        a
      qed
    cases .(⟨ e ⟩) (inr refl) v = -- i=0 holds
      proof:
        snd (((φ ∨ ⟨ e ⟩ ≈OI e) , h ⟨ e ⟩) ∙ ⟨ e ⟩) v
          ≡[ cong (snd (((φ ∨ ⟨ e ⟩ ≈OI e) , h ⟨ e ⟩) ∙ ⟨ e ⟩)) (equ ((fst φ or ⟨ e ⟩ ≈ ⟨ e ⟩)) v (∣ inr refl ∣)) ]≡
        snd (((φ ∨ ⟨ e ⟩ ≈OI e) , h ⟨ e ⟩) ∙ ⟨ e ⟩) (∣ inr refl ∣)
          ≡[ refl ]≡
        g ⟨ e ⟩ refl ⟨ e ⟩
          ≡[ refl ]≡
        a
      qed

  fill : (i : Int) → ⟦ a ∈ (A ∘ p) i ∣ ((φ ∨ i ≈OI e) , h i) ∙ ⟨ ! e ⟩ ↗ a ⟧
  fill i = (α e (p' i) (φ ∨ i ≈OI e) (h i) (a , hAtZero i))

  extendsF : (v : [ φ ])(i : Int) → f v i ≡ fst (fill i)
  extendsF v i = snd (fill i) ∣ inl v ∣

  atZero : fst (fill ⟨ e ⟩) ≡ a
  atZero = symm (snd (fill ⟨ e ⟩) ∣ inr refl ∣)

  result : ⟦ p ∈ Π (A ∘ p) ∣ ((φ , f ) ↗ p) & (p ⟨ e ⟩ ≈ a) ⟧
  fst result i = fst (fill i)
  fst (snd result) v = funext (extendsF v)
  snd (snd result) = atZero

  φAtOne : (φ ∨ ⟨ ! e ⟩ ≈OI e) ≡ φ
  φAtOne = cofEq (propext forwards backwards) where
    forwards : prf (fst (φ ∨ ⟨ ! e ⟩ ≈OI e)) → prf (fst φ)
    forwards v = ∥∥-rec (fst φ) cases v where
      cases : prf (fst φ) ⊎ (⟨ ! e ⟩ ≡ ⟨ e ⟩) → prf (fst φ)
      cases (inl p) = p
      cases (inr !e=e) = e≠!e (symm !e=e)
    backwards : prf (fst φ) → prf (fst (φ ∨ ⟨ ! e ⟩ ≈OI e))
    backwards v = ∣ inl v ∣

  propSwap :
    {A : Set}
    {P Q : Cof}
    (p : P ≡ Q)
    {f : [ P ] → A}
    (u : [ Q ])
    (v : [ P ])
    → -----------
    subst (λ φ → [ φ ] → A) p f u ≡ f v
  propSwap {A} {P} .{P} refl {f} u v = cong f (equ (fst P) u v)

  hAtOne : _≡_ {A = □ ((i : Int) → A (p i))} ((φ ∨ ⟨ ! e ⟩ ≈OI e) , h ⟨ ! e ⟩) (φ , f)
  hAtOne = Σext φAtOne (funext hIi≡fi) where
    hIi≡fi : (u : [ φ ]) → subst (λ φ₁ → [ φ₁ ] → (i : Int) → A (p i)) φAtOne (h ⟨ ! e ⟩) u ≡ f u
    hIi≡fi u =
      proof:
        subst (λ φ₁ → [ φ₁ ] → (i : Int) → A (p i)) φAtOne (h ⟨ ! e ⟩) u
          ≡[ propSwap φAtOne u  ∣ inl u ∣ ]≡
        h ⟨ ! e ⟩  ∣ inl u ∣
          ≡[ refl ]≡
        f u
      qed

  tupleFiddle :
    {A : Set}
    {B : A → Set}
    {C : (x : A) → B x → Set}
    {a a' : A}
    {b : B a}{b' : B a'}
    {c : C a b}{c' : C a' b'}
    (p : ((a , b) , c) ≡ ((a' , b') , c'))
    → -----------
    (a , (b , c)) ≡ (a' , (b' , c'))
  tupleFiddle refl = refl

  abstract
   fillAtOne : fst (fill ⟨ ! e ⟩) ≡ fst (α e p φ f (a , u))
   fillAtOne =
    proof:
      fst (fill ⟨ ! e ⟩)
        ≡[ refl ]≡
      fst (α e p (φ ∨ ⟨ ! e ⟩ ≈OI e) (h ⟨ ! e ⟩) (a , hAtZero ⟨ ! e ⟩))
        ≡[ cong (λ{(ψ , f , u) → fst (α e p ψ f (a , u))}) (tupleFiddle (Σext hAtOne (eq (((φ , f) ∙ ⟨ e ⟩ ↗ a))))) ]≡
      fst (α e p φ f (a , u)) 
    qed

abstract
 fill :
  {Γ : Set}
  {A : Γ → Set}
  (e : OI)
  (α : isFib A)
  (p : Int → Γ)
  → -----------
  Fill e (A ∘ p)
 fill {Γ} {A} e α p φ f a u = fst (fillInternal {A = A ∘ p} e (reindex A α p) id φ f a u)

abstract
 fillAtEnd :
  {Γ : Set}
  {A : Γ → Set}
  (e : OI)
  (α : isFib A)
  (p : Int → Γ)
  (φ : Cof)
  (f : [ φ ] → Π (A ∘ p))
  (a : A (p ⟨ e ⟩))
  (u : prf ((φ , f) ∙ ⟨ e ⟩ ↗ a))
  → -----------
  fst (fill {A = A} e α p φ f a u) ⟨ ! e ⟩ ≡ fst (α e p φ f (a , u))
 fillAtEnd {Γ} {A} e α p φ f a u = snd (fillInternal {A = A ∘ p} e (reindex A α p) id φ f a u)


