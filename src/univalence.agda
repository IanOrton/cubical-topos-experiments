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
module univalence where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.functions
open import Data.paths
open import equivs
open import glueing.core
open import glueing.strict
open import glueing.fix

IdU : {Γ : Set} → Fib Γ → Fib Γ → Set₁
IdU {Γ} Aα Bβ = Σ Pρ ∈ Fib (Γ × Int) , (reindex' Pρ (λ x → x , O) ≡ Aα) × (reindex' Pρ (λ x → x , I) ≡ Bβ)

idToEquiv : {Γ : Set}{A B : Fib Γ} → IdU A B → Σ f ∈ ((x : Γ) → (fst A x → fst B x)) , Equiv f
idToEquiv {Γ} ((P , ρ) , refl , refl) = (f , equiv) where
  <id,_> : Γ → Int → Γ × Int
  <id, x > i = (x , i)
  a~fa : (x : Γ)(a : P (x , O)) → (i : Int) → P (x , i)
  a~fa x a = fst (fill O' ρ (λ i → (x , i)) cofFalse ∅-elim a (λ ()))
  gb~b : (x : Γ)(b : P (x , I)) → (i : Int) → P (x , i)
  gb~b x b = fst (fill I' ρ (λ i → (x , i)) cofFalse ∅-elim b (λ ()))
  f : (x : Γ) → P (x , O) → P (x , I)
  f x a = fst (ρ O' <id, x > cofFalse ∅-elim (a , (λ ()))) --a~fa x a I
  g : (x : Γ) → P (x , I) → P (x , O)
  g x b = fst (ρ I' <id, x > cofFalse ∅-elim (b , (λ ()))) --gb~b x b O
  fgb~b : (x : Γ)(b : P (x , I)) → f x (g x b) ~ b
  fgb~b x b = let ρx = reindex P ρ <id, x > in
    transDep' {A = λ i → P (x , i)} {α = ρx}
      (fillPath ρx (g x b)) (fillPath' ρx b)
  gfa~a : (x : Γ)(a : P (x , O)) → g x (f x a) ~ a
  gfa~a x a = let ρx = reindex P ρ <id, x > in
    transDep {A = λ i → P (x , i)} {α = ρx}
      (fillPath' ρx (f x a)) (fillPath ρx a)
  qinv : (x : Γ) → Qinv (f x)
  qinv x = (g x) , fgb~b x , gfa~a x
  equiv : Equiv f
  equiv = qinv2equiv (reindex P ρ (λ x → (x , O))) (reindex P ρ (λ x → (x , I))) f qinv

data Tag : Set where
  i=O : Tag; i=I : Tag
decode : Set → Set → Tag → Set
decode A _ i=O = A
decode _ B i=I = B

makeC : {Γ : Set}(A B : Fib Γ) → Fib (res (Γ × Int) i=OI)
makeC {Γ} (A , α) (B , β) = C , μ where
  C : res (Γ × Int) i=OI → Set
  C ((x , i) , u) = decode (A x) (B x) (OI-elim (λ{ (inl x₁) → i=O ; (inr x₁) → i=I }) u)
  μ : isFib C
  μ e p = OI-elim cases (snd (p I)) where
    pZero : Int → Ω
    pZero i = snd (fst (p i)) ≈ O
    pOne : Int → Ω
    pOne i = snd (fst (p i)) ≈ I
    lem : (i : Int) → pZero i ≡ pZero I
    lem = cntd' pZero dec where
      dec : (i : Int) → prf (pZero i or ¬ (pZero i))
      dec i = ∥∥-elim
        (λ{ (inl x) → ∣ inl x ∣ ; (inr pi=I) → ∣ inr (λ pi=O → O≠I (trans pi=I (symm pi=O))) ∣ })
        (λ x x → eq (pZero i or ¬ (pZero i))) (snd (p i))
    lem' : (i : Int) → pOne i ≡ pOne I
    lem' = cntd' pOne dec where
      dec : (i : Int) → prf (pOne i or ¬ (pOne i))
      dec i = ∥∥-elim
        (λ{ (inl pi=O) → ∣ inr (λ pi=I → O≠I (trans pi=I (symm pi=O))) ∣ ; (inr pi=I) → ∣ inl pi=I ∣ })
        (λ x x → eq (pOne i or ¬ (pOne i))) (snd (p i))
    cases : prf (pZero I) ⊎ prf (pOne I) → Comp e (C ∘ p)
    cases (inl pI=O) = subst (Comp e) (symm Cp=Ap) (α e (fst ∘ fst ∘ p)) where
      pi=O : (i : Int) → prf (pZero i)
      pi=O i = subst prf (symm (lem i)) pI=O
      etaExp : (i : Int) → p i ≡ ((fst (fst (p i)) , O) , ∣ inl refl ∣)
      etaExp i = Σext (Σext refl (pi=O i)) (eq ((O ≈ O) or (O ≈ I)))
      Cp=Ap : C ∘ p ≡  A ∘ fst ∘ fst ∘ p
      Cp=Ap = funext (λ i → cong C (etaExp i))
    cases (inr pI=I) = subst (Comp e) (symm Cp=Bp) (β e (fst ∘ fst ∘ p)) where
      pi=I : (i : Int) → prf (snd (fst (p i)) ≈ I)
      pi=I i = subst prf (symm (lem' i)) pI=I
      etaExp : (i : Int) → p i ≡ ((fst (fst (p i)) , I) , ∣ inr refl ∣)
      etaExp i = Σext (Σext refl (pi=I i)) (eq ((I ≈ O) or (I ≈ I)))
      Cp=Bp : C ∘ p ≡  B ∘ fst ∘ fst ∘ p
      Cp=Bp = funext (λ i → cong C (etaExp i))


makeF' : {Γ : Set}(A B : Fib Γ)(f : (x : Γ) → fst A x → fst B x)(xi : Γ × Int)(u : [ i=OI xi ]) → fst (makeC A B) (xi , u) → fst B (fst xi)
makeF' {Γ} A B f (x , i) u = OI-elim-dep {B = λ u → C ((x , i) , u) → fst B x} cases u where
  C : res (Γ × Int) i=OI → Set
  C = fst (makeC A B)
  cases : {x : Γ}{i : Int}(u : (i ≡ O) ⊎ (i ≡ I)) → C ((x , i) , ∣ u ∣) → fst B x
  cases {x} (inl refl) a = f x a
  cases (inr refl) b = b

f'isEquiv : {Γ : Set}(A B : Fib Γ)
  (f : (x : Γ) → fst A x → fst B x)
  (e : Equiv f)
  (xi : Γ × Int)(u : [ i=OI xi ]) → Equiv' (makeF' A B f xi u)
f'isEquiv A B f e xi u = OI-elim-dep {B = λ u → Equiv' (makeF' A B f xi u)} cases u where
  cases : (v : (snd xi ≡ O) ⊎ (snd xi ≡ I)) → Equiv' (makeF' A B f xi ∣ v ∣)
  cases (inl refl) = e (fst xi)
  cases (inr refl) = idEquiv

equivToId : {Γ : Set}{A B : Fib Γ}
  (f : (x : Γ) → fst A x → fst B x)(equiv : Equiv f) → IdU A B
abstract
 equivToId {Γ} {A} {B} f equiv = Pρ , PO=A , PI=B where
  C : Fib (res (Γ × Int) i=OI)
  C = makeC A B
  B' : Fib (Γ × Int)
  B' = reindex' B fst
  f' : (xi : Γ × Int)(u : [ i=OI xi ]) → fst C (xi , u) → fst B (fst xi)
  f' = makeF' A B f
  f'equiv : (xi : Γ × Int) → Equiv (f' xi)
  f'equiv = f'isEquiv A B f equiv
  Pρ : Fib (Γ × Int)
  Pρ = SGlueFib i=OI C B' f' f'equiv
  inlrefl : Γ → res (Γ × Int) i=OI
  inlrefl x = (x , O) , ∣ inl refl ∣
  PO=A : reindex' Pρ (λ x → x , O) ≡ A
  PO=A =
    proof:
        reindex' Pρ (λ x → x , O)
      ≡[ refl ]≡
        reindex' (reindex' Pρ fst) inlrefl
      ≡[ cong (λ C → reindex' C inlrefl) (SGlueReindex i=OI C B' f' f'equiv) ]≡
        reindex' C inlrefl
      ≡[ refl ]≡
        A
    qed
  inrrefl : Γ → res (Γ × Int) i=OI
  inrrefl x = (x , I) , ∣ inr refl ∣
  PI=B : reindex' Pρ (λ x → x , I) ≡ B
  PI=B =
    proof:
        reindex' Pρ (λ x → x , I)
      ≡[ refl ]≡
        reindex' (reindex' Pρ fst) inrrefl
      ≡[ cong (λ C → reindex' C inrrefl) (SGlueReindex i=OI C B' f' f'equiv) ]≡
        reindex' C inrrefl
      ≡[ refl ]≡
        B
    qed

-- Now we show uaβ. This follows from the following property:
compOIProperty :  {Γ : Set}{A B : Fib Γ}
  (f : (x : Γ) → fst A x → fst B x)
  → IdU A B → Set
compOIProperty {Γ} {A} {B} f Pρ = (x : Γ)(a : (fst (fst Pρ) ∘ < x ,id>) O)
  → fst (snd (fst Pρ) O' < x ,id> cofFalse ∅-elim (a , (λ ())))
      ≡ coe (symm (cong (λ B → fst B x) (snd (snd Pρ))))
          (trivComp B I' x (trivComp B O' x
            (f x (coe (cong (λ A → fst A x) (fst (snd Pρ))) a))))

-- equivToId f equiv has this property:
uaβhelper4 : {Γ : Set}{A B : Fib Γ}
  (f : (x : Γ) → fst A x → fst B x)(equiv : Equiv f)
  → compOIProperty {Γ} {A} {B} f (equivToId {Γ} {A} {B} f equiv)
abstract
 uaβhelper4 {Γ} {A} {B} f equiv x a =
 
  proof:
  
      compOI (fst (equivToId {Γ} {A} {B} f equiv)) x a
      
    ≡[ cong (λ f → fst (f cofFalse ∅-elim (a , λ ()))) (uaβhelper C B' f' e' x) ]≡
    
      compOI (SGlueFib' i=OI C B' f' e') x a
      
    ≡[ uaβhelper2 C B' f' e' x a ]≡
    
      str f' (x , I) (compOI (GlueFib i=OI C B' f' e') x (unstr f' (x , O) a))

    ≡[ strIsUnglue f' (x , I) ∣ inr refl ∣ (compOI (GlueFib i=OI C B' f' e') x (unstr f' (x , O) a)) ]≡
    
      coe (symm strictB)
        (fst (compOI (GlueFib i=OI C B' f' e') x (unstr f' (x , O) a)) ∣ inr refl ∣)
        
    ≡[ cong (λ a' → coe (symm strictB)
        (fst (compOI (GlueFib i=OI C B' f' e') x a') ∣ inr refl ∣)) (unstrIsGlue f' (x , O) ∣ inl refl ∣ a) ]≡
        
      coe (symm strictB)
        (fst (compOI (GlueFib i=OI C B' f' e') x
          (glue {Φ = i=OI} f' ((x , O) , ∣ inl refl ∣) (coe strictA a))) ∣ inr refl ∣)
        
    ≡[ cong (coe (symm strictB)) (uaβhelper3 C B' f' e' x (coe strictA a)) ]≡
    
      coe (symm strictB) (trivComp B I' x (trivComp B O' x (f x (coe strictA a))))
      
    ≡[ cong (λ p → coe p (trivComp B I' x (trivComp B O' x (f x (coe strictA a))))) (uip (symm strictB) (symm (cong (λ B → fst B x) (snd (snd (equivToId {Γ} {A} {B} f equiv)))))) ]≡
    
      coe (symm (cong (λ B → fst B x) (snd (snd (equivToId {Γ} {A} {B} f equiv))))) (trivComp B I' x (trivComp B O' x (f x (coe strictA a))))
      
    ≡[ cong (λ p → coe (symm (cong (λ B → fst B x) (snd (snd (equivToId {Γ} {A} {B} f equiv))))) (trivComp B I' x (trivComp B O' x (f x (coe p a))))) (uip strictA (cong (λ A → fst A x) (fst (snd (equivToId {Γ} {A} {B} f equiv))))) ]≡
    
      coe (symm (cong (λ B → fst B x) (snd (snd (equivToId {Γ} {A} {B} f equiv))))) (trivComp B I' x (trivComp B O' x (f x (coe ((cong (λ A → fst A x) (fst (snd (equivToId {Γ} {A} {B} f equiv))))) a))))
      
  qed where
    C : Fib (res (Γ × Int) i=OI)
    C = makeC A B
    B' : Fib (Γ × Int)
    B' = reindex' B fst
    f' : (x : Γ × Int)(u : [ i=OI x ]) → fst C (x , u) → fst B' x
    f' = makeF' A B f
    e' : (x : Γ × Int)(u : [ i=OI x ]) → Equiv' (f' x u)
    e' = f'isEquiv A B f equiv
    strictA = strictness i=OI (fst C) (fst B ∘ fst) f' (x , O) ∣ inl refl ∣
    strictB = strictness i=OI (fst C) (fst B ∘ fst) f' (x , I) ∣ inr refl ∣


-- There is always a path from a to trivComp (trivComp a):
abstract
 helper : {Γ : Set}(A : Fib Γ)(x : Γ)(a : fst A x)
  → a ~ trivComp A I' x (trivComp A O' x a)
 helper (A , α) x a = (λ i → fst (p i)) , pO=a , pI=rhs where
  filler = fill O' α (λ _ → x) cofFalse ∅-elim a (λ ())
  cases : {i : Int} → (i ≡ O) ⊎ (i ≡ I) → Π (A ∘ (λ _ → x))
  cases (inl _) _ = a
  cases (inr refl) = fst (fill I' α (λ _ → x) cofFalse ∅-elim (fst filler I) (λ ()))
  left : {i : Int}{l : i ≡ O} → snd (((i ≈O) ∨ (i ≈I) , OI-elim cases) ∙ O) ∣ inl l ∣ ≡ fst filler i
  left {l = refl} = symm (snd (snd filler))
  right : {i : Int}{r : i ≡ I} → OI-elim cases ∣ inr r ∣ I ≡ fst filler i
  right {r = refl} = snd (snd (fill I' α (λ _ → x) cofFalse ∅-elim (fst filler I) (λ ())))
  p = λ i →  α I' (λ _ → x) ((i ≈O) ∨ (i ≈I)) (OI-elim cases)
    (fst filler i , or-elim-eq (λ u → OI-elim cases u I) (fst filler i)
    (λ {l} → left {l = l}) (λ {r} → right {r = r}))
  pO=a : fst (p O) ≡ a
  pO=a = symm (snd (p O) ∣ inl refl ∣)
  pI=rhs : fst (p I) ≡ trivComp (A , α) I' x (trivComp (A , α) O' x a)
  pI=rhs =
    proof:
        fst (p I)
      ≡[ symm (snd (p I) ∣ inr refl ∣) ]≡
        fst (fill I' α (λ _ → x) cofFalse ∅-elim (fst filler I) (λ ())) O
      ≡[ fillAtEnd I' α (λ _ → x) cofFalse ∅-elim (fst filler I) (λ ()) ]≡
        trivComp (A , α) I' x (fst filler I)
      ≡[ cong (trivComp (A , α) I' x) (fillAtEnd O' α (λ _ → x) cofFalse ∅-elim a (λ ())) ]≡
        trivComp (A , α) I' x (trivComp (A , α) O' x a)
    qed

-- Define coerce as in the paper:
coerce : {Γ : Set}{A B : Fib Γ} → IdU A B → (x : Γ) → fst A x → fst B x
coerce P = fst (idToEquiv P)

-- Any IdU A B with the compOIProperty satisfies f ~ coerce P:
uaβ' : {Γ : Set}(A B : Fib Γ)
  (f : (x : Γ) → fst A x → fst B x)
  (e : Equiv f)
  (P : IdU A B)
  → ----------------
  compOIProperty {Γ} {A} {B} f P → f ~ coerce P
uaβ' {Γ} _ _ f e ((P , ρ) , refl , refl) h =
  funextPath (λ x → funextPath (λ a →
    subst (λ b → f x a ~ b) (symm (h x a)) (helper (reindex' (P , ρ) (λ x → x , I)) x (f x a))))

-- Therefore equivToId f e satisfies f ~ coerce (equivToId f e)
uaβ : {Γ : Set}(A B : Fib Γ)
  (f : (x : Γ) → fst A x → fst B x)
  (e : Equiv f)
  → ----------------
  f ~ coerce (equivToId {Γ} {A} {B} f e)
uaβ {Γ} A B f e = uaβ' A B f e (equivToId {Γ} {A} {B} f e) (uaβhelper4 {Γ} {A} {B} f e)
