----------------------------------------------------------------------
-- This Agda code is designed to accompany the paper "Axioms for
-- Modelling Cubical Type Theory in a Topos". It is currently a work
-- in progress and still includes postulates/holes in certain places.
-- It also needs some tidying up and possibily reorganisation.
--
-- The idea for getting an impredicative universe of propositions Ω
-- comes from Martin Escardo, more details can be found at:
--
--          http://www.cs.bham.ac.uk/~mhe/impredicativity/          
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module univalence-working where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.products
open import Data.paths
open import equivs
open import glueing

IdU : (A B : Set) → Set₁
IdU A B = Σ P ∈ (Int → Set) , (P O ≡ A) × (P I ≡ B)


idToEquiv : {A B : Set}(P : IdU A B)(ρ : Fib (fst P)) → Σ f ∈ (A → B) , Equiv f ×
    ((a : A) → _~~_ {A = fst P} (coe (symm (fst (snd P))) a) ((coe (symm (snd (snd P))) (f a))))
idToEquiv (P , refl , refl) ρ = (fst fequiv , snd fequiv , a~~fa) where
  a~fa : (a : P O) → Π P
  a~fa a = fst (fill O' ρ id cofFalse ∅-elim a (λ ()))
  gb~b : (b : P I) → Π P
  gb~b b = fst (fill I' ρ id cofFalse ∅-elim b (λ ()))
  f : P O → P I
  f a = a~fa a I
  g : P I → P O
  g b = gb~b b O
  fgb~b : (b : P I) → f (g b) ~ b
  fgb~b b = ((λ i → fst (filling i)) , atZero , atOne) where
    cases : (i : Int) → (i ≡ O) ⊎ (i ≡ I) → Π P
    cases _ (inl i≡O) = a~fa (g b)
    cases _ (inr i≡I) = gb~b b
    casesAgree : (i : Int)(x x' : (i ≡ O) ⊎ (i ≡ I)) → cases i x ≡ cases i x'
    casesAgree _ (inl i≡O) (inl i≡O') = refl
    casesAgree _ (inl i≡O) (inr i≡I) = ∅-elim (O≠I (trans i≡I (symm i≡O)))
    casesAgree _ (inr i≡I) (inl i≡O) = ∅-elim (O≠I (trans i≡I (symm i≡O)))
    casesAgree _ (inr i≡I) (inr i≡I') = refl
    q : (i : Int) → [ i ≈O ∨ i ≈I ] → Π P
    q i u = ∥∥-elim (cases i) (casesAgree i) u
    extends : (i : Int) → prf (((i ≈O ∨ i ≈I) , (λ u → ∥∥-elim (cases i) (casesAgree i) u)) ∙ O ↗ g b)
    extends i u = or-elim-eq (λ u → q i u O) (g b) (snd (snd (fill {A = P} O' ρ id cofFalse ∅-elim (g b) (λ ())))) refl u
    filling : (i : Int) → ⟦ b ∈ (P I) ∣ ((i ≈O ∨ i ≈I) , q i) ∙ I ↗ b ⟧
    filling i = ρ O' id (i ≈O ∨ i ≈I) (q i) (g b , extends i)
    atZero : fst (filling O) ≡ f (g b)
    atZero = symm (snd (filling O) ∣ inl refl ∣)
    atOne : fst (filling I) ≡ b
    atOne = trans qI≡b fillingI=qI  where
      qI≡b : q I ∣ inr refl ∣ I ≡ b
      qI≡b = snd (snd (fill {A = P} I' ρ id cofFalse ∅-elim b (λ ())))
      fillingI=qI : fst (filling I) ≡ q I ∣ inr refl ∣ I
      fillingI=qI = symm (snd (filling I) ∣ inr refl ∣)
  gfa~a : (a : P O) → g (f a) ~ a
  gfa~a a = ((λ i → fst (filling i)) , atZero , atOne) where
    cases : (i : Int) → (i ≡ O) ⊎ (i ≡ I) → Π P
    cases _ (inl i≡O) = gb~b (f a)
    cases _ (inr i≡I) = a~fa a
    casesAgree : (i : Int)(x x' : (i ≡ O) ⊎ (i ≡ I)) → cases i x ≡ cases i x'
    casesAgree _ (inl i≡O) (inl i≡O') = refl
    casesAgree _ (inl i≡O) (inr i≡I) = ∅-elim (O≠I (trans i≡I (symm i≡O)))
    casesAgree _ (inr i≡I) (inl i≡O) = ∅-elim (O≠I (trans i≡I (symm i≡O)))
    casesAgree _ (inr i≡I) (inr i≡I') = refl
    q : (i : Int) → [ i ≈O ∨ i ≈I ] → Π P
    q i u = ∥∥-elim (cases i) (casesAgree i) u
    extends : (i : Int) → prf (((i ≈O ∨ i ≈I) , (λ u → ∥∥-elim (cases i) (casesAgree i) u)) ∙ I ↗ f a)
    extends i u = or-elim-eq (λ u → q i u I) (f a) (snd (snd (fill {A = P} I' ρ id cofFalse ∅-elim (f a) (λ ())))) refl u
    filling : (i : Int) → ⟦ a ∈ (P O) ∣ ((i ≈O ∨ i ≈I) , q i) ∙ O ↗ a ⟧
    filling i = ρ I' id (i ≈O ∨ i ≈I) (q i) (f a , extends i)
    atZero : fst (filling O) ≡ g (f a)
    atZero = symm (snd (filling O) ∣ inl refl ∣)
    atOne : fst (filling I) ≡ a
    atOne = trans qI≡b fillingI=qI  where
      qI≡b : q I ∣ inr refl ∣ O ≡ a
      qI≡b = snd (snd (fill {A = P} O' ρ id cofFalse ∅-elim a (λ ())))
      fillingI=qI : fst (filling I) ≡ q I ∣ inr refl ∣ O
      fillingI=qI = symm (snd (filling I) ∣ inr refl ∣)
  α : Fib {Γ = Unit} (λ _ → P O)
  α e p = ρ e (λ _ → O) 
  β : Fib {Γ = Unit} (λ _ → P I)
  β e p = ρ e (λ _ → I)
  qinv : Qinv f
  fst qinv = g
  fst (snd qinv) = fgb~b
  snd (snd qinv) = gfa~a
  equivf : Equiv f
  equivf = qinv2equiv α β (λ _ → f) tt qinv
  fequiv : Σ f ∈ (P O → P I) , Equiv f
  fequiv = (f , equivf) --subst (λ B →  Σ f ∈ (P O → P ) , Equiv f) PI≡B (subst (λ A →  Σ f ∈ (A → P I) , Equiv f) PO≡A (f , equivf))
  a~~fa : (a : P O) → _~~_ {A = P} a (f a)
  a~~fa a = (fst filling , (snd (snd filling)) , refl) where
    filling : ⟦ p ∈ (Π P) ∣ (cofFalse , ∅-elim) ↗ p & p O ≈ a ⟧
    filling = fill O' ρ id cofFalse ∅-elim a (λ ())



Φ : Int → Cof
Φ i = (i ≈O) ∨ (i ≈I)


data Tag : Set where
  i=O : Tag; i=1 : Tag
decode : Set → Set → Tag → Set
decode A _ i=O = A
decode _ B i=1 = B

makeC : (A B : Set)(f : A → B) → res Int Φ → Set
makeC A B f (i , u) = decode A B (OI-elim cases u) where
    cases : (i ≡ O) ⊎ (i ≡ I) → Tag
    cases (inl _) = i=O
    cases (inr _) = i=1




makeF' : (A B : Set)(f : A → B)(i : Int)(u : [ Φ i ]) → makeC A B f (i , u) → B
makeF' A B f i u = OI-elim-dep {B = λ u → C (i , u) → B} cases u where
  C : res Int Φ → Set
  C = makeC A B f
  cases : {i : Int}(u : (i ≡ O) ⊎ (i ≡ I)) → C (i , ∣ u ∣) → B
  cases (inl refl) a = f a -- f (subst (λ u → C (i , u)) (equ (fst (Φ i)) u ∣ inl v ∣) a)
  cases (inr refl) b = b -- subst (λ u → C (i , u)) (equ (fst (Φ i)) u ∣ inr v ∣) b
  

-- equivToId1 : {A B : Set}{α : Fib {Γ = Unit} (λ _ → A)}{β : Fib {Γ = Unit} (λ _ → B)}
--   (f : A → B)(equiv : Equiv f) → IdU A B
-- equivToId1 {A} {B} {α} {β} f equivf = (SGlue Φ C (λ _ → B) f' , atO , atI) where
--   C : res Int Φ → Set
--   C = makeC A B f
--   f' : (i : Int)(u : [ Φ i ]) → C (i , u) → B
--   f' = makeF' A B f
--   atO : SGlue Φ C (λ _ → B) f' O ≡ A
--   atO = strictness Φ C (λ _ → B) f' O ∣ inl refl ∣
--   atI : SGlue Φ C (λ _ → B) f' I ≡ B
--   atI = strictness Φ C (λ _ → B) f' I ∣ inr refl ∣



-- equivToId2 : {A B : Set}{α : Fib {Γ = Unit} (λ _ → A)}{β : Fib {Γ = Unit} (λ _ → B)}
--   (f : A → B)(equiv : Equiv f) →  Fib (fst (equivToId1 {α = α} f equiv))
-- equivToId2 {A} {B} {α} {β} f equivf = FibSGlue {Φ = Φ} f' (λ x u → equivf' x u) fibC (λ e p → β e (λ _ → tt)) where
--   C : res Int Φ → Set
--   C = makeC A B f
--   f' : (i : Int)(u : [ Φ i ]) → C (i , u) → B
--   f' = makeF' A B f
--   atO : SGlue Φ C (λ _ → B) f' O ≡ A
--   atO = strictness Φ C (λ _ → B) f' O ∣ inl refl ∣
--   atI : SGlue Φ C (λ _ → B) f' I ≡ B
--   atI = strictness Φ C (λ _ → B) f' I ∣ inr refl ∣
--   P : IdU A B
--   P = (SGlue Φ C (λ _ → B) f' , atO , atI)
--   equivId : Equiv id
--   equivId = qinv2equiv β β (λ _ → id) tt (id , ((λ b → reflPath {Γ = Unit} {A = (λ _ → B)} b) , (λ b → reflPath {Γ = Unit} {A = (λ _ → B)} b)))
--   equivf' : (i : Int)(u : [ Φ i ]) → Equiv (f' i u)
--   equivf' i u = OI-elim cases u where
--     cases : (i ≡ O) ⊎ (i ≡ I) → Equiv (f' i u)
--     cases (inl v) = subst (λ u → Equiv (f' i u)) (equ (fst (Φ i)) ∣ inl v ∣ u) equivf
--     cases (inr v) = subst (λ u → Equiv (f' i u)) (equ (fst (Φ i)) ∣ inr v ∣ u) equivId
--   fibC : Fib C
--   fibC e p = OI-elim compCases (snd (p I)) where
--     compEq : {Γ : Set}(A B : Int → Set) → A ≡ B → Comp e A → Comp e B
--     compEq A .A refl α = α
--     compCases : (fst (p I) ≡ O) ⊎ (fst (p I) ≡ I) → Comp e (C ∘ p)
--     compCases (inl pI≡O) = compEq {Γ = res Int Φ} (λ _ → A) (C ∘ p) (funext eqFibers) (α e (λ _ → tt)) where
--       constO : Int → Ω
--       constO i = p i ≈ (O , ∣ inl refl ∣)
--       pConst : (i : Int) → constO i ≡ constO I
--       pConst = cntd' constO (λ i → OI-elim cases (snd (p i))) where
--         cases : {i : Int} → (fst (p i) ≡ O) ⊎ (fst (p i) ≡ I) → prf((constO i) or ¬(constO i))
--         cases (inl pi≡O) = ∣ inl (Σext pi≡O (eq (O ≈ O or O ≈ I))) ∣
--         cases (inr pi≡I) = ∣ inr (λ u → ∅-elim (O≠I (trans pi≡I (symm (Σeq₁ u))))) ∣
--       pAti : (i : Int) → prf (constO i)
--       pAti i = subst prf (symm (pConst i)) (Σext pI≡O (eq (O ≈ O or O ≈ I)))
--       eqFibers : (i : Int) → A ≡ (C ∘ p) i
--       eqFibers i = subst (λ pi → A ≡ C pi) (symm (pAti i)) refl
--     compCases (inr pI≡I) = compEq {Γ = res Int Φ} (λ _ → B) (C ∘ p) (funext eqFibers) (β e (λ _ → tt)) where
--       constI : Int → Ω
--       constI i = p i ≈ (I , ∣ inr refl ∣)
--       pConst : (i : Int) → constI i ≡ constI I
--       pConst = cntd' constI (λ i → OI-elim cases (snd (p i))) where
--         cases : {i : Int} → (fst (p i) ≡ O) ⊎ (fst (p i) ≡ I) → prf((constI i) or ¬(constI i))
--         cases (inl pi≡O) = ∣ inr (λ u → ∅-elim (O≠I (trans (Σeq₁ u) (symm pi≡O)))) ∣
--         cases (inr pi≡I) = ∣ inl (Σext pi≡I (eq (I ≈ O or I ≈ I))) ∣
--       pAti : (i : Int) → prf (constI i)
--       pAti i = subst prf (symm (pConst i)) (Σext pI≡I (eq (I ≈ O or I ≈ I)))
--       eqFibers : (i : Int) → B ≡ (C ∘ p) i
--       eqFibers i = subst (λ pi → B ≡ C pi) (symm (pAti i)) refl



equivToId : {A B : Set}{α : Fib {Γ = Unit} (λ _ → A)}{β : Fib {Γ = Unit} (λ _ → B)}
  (f : A → B)(equiv : Equiv f) → Σ P ∈ (IdU A B) , Σ ρ ∈ Fib (fst P) ,
    ((a : A) → _~~_ {A = fst P} (coe (symm (fst (snd P))) a) ((coe (symm (snd (snd P))) (f a))))
equivToId {A} {B} {α} {β} f equivf = (P , fibP , fPath) where
  C : res Int Φ → Set
  C = makeC A B f
  f' : (i : Int)(u : [ Φ i ]) → C (i , u) → B
  f' = makeF' A B f
  atO : SGlue Φ C (λ _ → B) f' O ≡ A
  atO = strictness Φ C (λ _ → B) f' O ∣ inl refl ∣
  atI : SGlue Φ C (λ _ → B) f' I ≡ B
  atI = strictness Φ C (λ _ → B) f' I ∣ inr refl ∣
  P : IdU A B
  P = (SGlue Φ C (λ _ → B) f' , atO , atI)
  fPath : (a : A) → _~~_ {A = fst P} (coe (symm (fst (snd P))) a) (coe (symm (snd (snd P))) (f a))
  fPath a = (path , pathAtO , pathAtI) where
    q : (i : Int)(u : [ Φ i ]) → C (i , u)
    q i u = OI-elim-dep {B = λ u → C (i , u)} cases u where --(λ{ (inl x) → subst (λ u → C (i , u)) (equ (fst (Φ i)) ∣ inl x ∣ u) a ; (inr x) → subst (λ u → C (i , u)) (equ (fst (Φ i)) ∣ inr x ∣ u) (f a) }) u
      cases : {i : Int}(u : (i ≡ O) ⊎ (i ≡ I)) → C (i , ∣ u ∣)
      cases (inl refl) = a
      cases (inr refl) = f a
    fq≡fa : (i : Int)(x : [ Φ i ]) → f' i x (q i x) ≡ f a
    fq≡fa i u = OI-elim-dep {B = λ u → f' i u (q i u) ≡ f a} cases u where --or-elim-eq (λ u → f' i u (q i u)) (f a) refl refl u
      cases : {i : Int}(v : (i ≡ O) ⊎ (i ≡ I)) → f' i ∣ v ∣ (q i ∣ v ∣) ≡ f a
      cases (inl refl) = refl
      cases (inr refl) = refl
    path : (i : Int) → fst P i
    path i = str {Φ = Φ} {A = C} {B = λ _ → B} f' i (q i , (f a) , fq≡fa i)
    pathAtO : path O ≡ coe (symm (fst (snd P))) a
    pathAtO = strIsUnglue {Φ = Φ} {A = C} {B = λ _ → B} f' O ∣ inl refl ∣ (q O , (f a) , fq≡fa O)
    pathAtI : path I ≡ coe (symm (snd (snd P))) (f a)
    pathAtI = strIsUnglue {Φ = Φ} {A = C} {B = λ _ → B} f' I ∣ inr refl ∣ (q I , (f a) , fq≡fa I)
  equivId : Equiv id
  equivId = qinv2equiv β β (λ _ → id) tt (id , ((λ b → reflPath {Γ = Unit} {A = (λ _ → B)} b) , (λ b → reflPath {Γ = Unit} {A = (λ _ → B)} b)))
  equivf' : (i : Int)(u : [ Φ i ]) → Equiv (f' i u)
  equivf' i u = OI-elim-dep {B = λ u → Equiv (f' i u)} cases u where
    cases : {i : Int}(v : (i ≡ O) ⊎ (i ≡ I)) → Equiv (f' i ∣ v ∣)
    cases (inl refl) = equivf
    cases (inr refl) = equivId
  fibC : Fib C
  fibC e p = OI-elim compCases (snd (p I)) where
    compEq : {Γ : Set}(A B : Int → Set) → A ≡ B → Comp e A → Comp e B
    compEq A .A refl α = α
    compCases : (fst (p I) ≡ O) ⊎ (fst (p I) ≡ I) → Comp e (C ∘ p)
    compCases (inl pI≡O) = compEq {Γ = res Int Φ} (λ _ → A) (C ∘ p) (funext eqFibers) (α e (λ _ → tt)) where
      constO : Int → Ω
      constO i = p i ≈ (O , ∣ inl refl ∣)
      pConst : (i : Int) → constO i ≡ constO I
      pConst = cntd' constO (λ i → OI-elim cases (snd (p i))) where
        cases : {i : Int} → (fst (p i) ≡ O) ⊎ (fst (p i) ≡ I) → prf((constO i) or ¬(constO i))
        cases (inl pi≡O) = ∣ inl (Σext pi≡O (eq (O ≈ O or O ≈ I))) ∣
        cases (inr pi≡I) = ∣ inr (λ u → ∅-elim (O≠I (trans pi≡I (symm (Σeq₁ u))))) ∣
      pAti : (i : Int) → prf (constO i)
      pAti i = subst prf (symm (pConst i)) (Σext pI≡O (eq (O ≈ O or O ≈ I)))
      eqFibers : (i : Int) → A ≡ (C ∘ p) i
      eqFibers i = subst (λ pi → A ≡ C pi) (symm (pAti i)) refl
    compCases (inr pI≡I) = compEq {Γ = res Int Φ} (λ _ → B) (C ∘ p) (funext eqFibers) (β e (λ _ → tt)) where
      constI : Int → Ω
      constI i = p i ≈ (I , ∣ inr refl ∣)
      pConst : (i : Int) → constI i ≡ constI I
      pConst = cntd' constI (λ i → OI-elim cases (snd (p i))) where
        cases : {i : Int} → (fst (p i) ≡ O) ⊎ (fst (p i) ≡ I) → prf((constI i) or ¬(constI i))
        cases (inl pi≡O) = ∣ inr (λ u → ∅-elim (O≠I (trans (Σeq₁ u) (symm pi≡O)))) ∣
        cases (inr pi≡I) = ∣ inl (Σext pi≡I (eq (I ≈ O or I ≈ I))) ∣
      pAti : (i : Int) → prf (constI i)
      pAti i = subst prf (symm (pConst i)) (Σext pI≡I (eq (I ≈ O or I ≈ I)))
      eqFibers : (i : Int) → B ≡ (C ∘ p) i
      eqFibers i = subst (λ pi → B ≡ C pi) (symm (pAti i)) refl
  fibP : Fib (fst P)
  fibP = FibSGlue {Φ = Φ} f' (λ x u → equivf' x u) fibC (λ e p → β e (λ _ → tt))


    

pathToPath :
  {A B : Set}
  (P : IdU A B)
  (ρ : Fib (fst P))
  → -------------
  Σ P' ∈ (IdU A B) , Fib (fst P')
pathToPath {A} {B} P ρ =
  let (f , equiv , _) = idToEquiv P ρ in
  let (P' , ρ' , _ ) = equivToId {α = α} {β} f equiv in
  (P' , ρ')
    where
      α : Fib (λ _ → A)
      α = subst (λ A → Fib {Γ = Unit} (λ _ → A)) (fst (snd P)) (λ e p → ρ e (λ _ → O))
      β : Fib (λ _ → B)
      β = subst (λ B → Fib {Γ = Unit} (λ _ → B)) (snd (snd P)) (λ e p → ρ e (λ _ → I))

equivToEquiv :
  {A B : Set}
  {α : Fib {Γ = Unit} (λ _ → A)}
  {β : Fib {Γ = Unit} (λ _ → B)}
  (f : A → B)
  (e : Equiv f)
  → -------------
  Σ f' ∈ (A → B) , Equiv f'
equivToEquiv {A} {B} {α} {β} f e =
  let (P , ρ , _) = equivToId {α = α} {β} f e in
  let (f' , e' , _) = idToEquiv P ρ in
  (f' , e')



-- equivInv :
--   {A B : Set}
--   {α : Fib {Γ = Unit} (λ _ → A)}
--   {β : Fib {Γ = Unit} (λ _ → B)}
--   (f : A → B)
--   (e : Equiv f)
--   → ---------------
--   f ~ fst (equivToEquiv {A} {B} {α} {β} f e)
-- equivInv {A} {B} {α = α} {β} f e = funextPath fa~ga where
--   coePath : {A B : Set}{eq : A ≡ B}{a a' : A} → coe eq a ~ coe eq a' → a ~ a'
--   coePath {eq = refl} p = p
--   fa~ga : (a : A) → f a ~ fst (equivToEquiv f e) a
--   fa~ga a =
--     let (P , ρ , a~~fa) = equivToId {α = α} {β} f e in
--     let (f' , e' , a~~ga) = idToEquiv P ρ in
--     let fa~gaInP = transDep' {α = ρ} (a~~fa a) (a~~ga a) in
--     coePath {eq = (symm (snd (snd (fst (equivToId {α = α} {β = β} f e)))))} fa~gaInP
