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
module univalence.inverses' where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.id
open import Data.paths
open import Data.products
open import equivs
open import glueing
open import univalence.core 
open import univalence.inverses

----------------------------------------------------------------------
-- Mere propositions
----------------------------------------------------------------------
isProp : (A : Set) → Set
isProp A = (a a' : A) → a ~ a'

----------------------------------------------------------------------
-- Being an equiv is a mere proposition
----------------------------------------------------------------------
isPropEquiv : {A B : Set}(f : A → B) → isProp (Equiv f)
isPropEquiv {A} {B} f e e' = funextPath {!!} where
  path : (b : B) → e b ~ e' b
  path b = let tt = λ i → fill O' {!!}  (λ _ → tt) (i ≈O ∨ i ≈I) {!!} b {!!} in {!!}
--   fst (path b) i = let rr = snd (e b) (fst (e' b)) in (fst rr i , {!!}) where
--     square : (a : Fiber f b) → fst (snd (e b) (fst (e' b))) i ~ a
--     fst (square a) j = {!comp !}

-- --fst (fill {A = λ{tt → Fiber f b}} O' {!!} (λ _ → tt) (i ≈O ∨ i ≈I) (OI-elim cases) (fst (snd (e b) (fst (e' b))) i) extends) where
--       -- cases : {i : Int} → (i ≡ O) ⊎ (i ≡ I) → Int → Fiber f b
--       -- cases (inl refl) = fst (snd (e  b) a)
--       -- cases (inr refl) = fst (snd (e' b) a)
--       -- extends : prf (((i ≈O) ∨ (i ≈I) , OI-elim cases) ∙ O ↗ fst (snd (e b) (fst (e' b))) i)
--       -- extends u = OI-elim-dep {B = λ u → OI-elim cases u O ≡ fst (snd (e b) (fst (e' b))) i} {!cases'!} u where
--       --   cases' : {i : Int}(v : (i ≡ O) ⊎ (i ≡ I)) → OI-elim cases ∣ v ∣ O ≡ fst (snd (e b) (fst (e' b))) i
--       --   cases' (inl refl) =
--       --     proof: fst (snd (e b) a) O
--       --      ≡[ fst (snd (snd (e b) a)) ]≡
--       --      fst (e b)
--       --      ≡[ symm (fst (snd ((snd (e b) (fst (e' b)))))) ]≡
--       --      fst (snd (e b) (fst (e' b))) O qed
--       --   cases' (inr refl) =
--       --     proof: fst (snd (e' b) a) O
--       --      ≡[ fst (snd (snd (e' b) a)) ]≡
--       --      fst (e' b)
--       --      ≡[ symm (snd (snd ((snd (e b) (fst (e' b)))))) ]≡
--       --      fst (snd (e b) (fst (e' b))) I qed
--     fst (snd (square a)) = {!!}
--     snd (snd (square a)) = {!!}
--   snd (path b) = {!!}



----------------------------------------------------------------------
-- Being a fibration is a mere proposition
----------------------------------------------------------------------
pathExtFib : {Γ : Set}{A : Γ → Set}{α α' : Fib A} →
  ((e : OI)(p : Int → Γ)(φ : Cof)(f : [ φ ] → Π (A ∘ p))
  (a₀ : ⟦ a ∈ (A (p ⟨ e ⟩)) ∣ (φ , f) ∙ ⟨ e ⟩ ↗ a ⟧) → α e p φ f a₀ ~ α' e p φ f a₀) → α ~ α'
fst (pathExtFib pointwise) i e p φ f a₀ = fst (pointwise e p φ f a₀) i
fst (snd (pathExtFib pointwise)) =
 funext (λ e → funext (λ p → funext (λ φ →
  funext (λ f → funext (λ a₀ → fst (snd (pointwise e p φ f a₀)))))))
snd (snd (pathExtFib pointwise)) = 
 funext (λ e → funext (λ p → funext (λ φ →
  funext (λ f → funext (λ a₀ → snd (snd (pointwise e p φ f a₀)))))))


FibIsProp : {Γ : Set}(A : Γ → Set) → isProp (Fib A)
FibIsProp {Γ} A α α' = pathExtFib {A = A} path where
  path : (e : OI) (p : Int → Γ) (φ : Cof)(f : [ φ ] → Π (A ∘ p))
      (a₀ : set (A (p ⟨ e ⟩)) (_↗_ ((φ , f) ∙ ⟨ e ⟩))) →
      α e p φ f a₀ ~ α' e p φ f a₀
  path e p φ f a₀ = (a₁' , atZero , atOne) where
      left : {i : Int} → [ (i ≈O) ∨ (i ≈I) ] → Π (A ∘ p)
      left {i} u = OI-elim cases u where
        cases : (i ≡ O) ⊎ (i ≡ I) → (i₁ : Int) → (A ∘ p) i₁
        cases (inl x) = fst (fill {A = A} e α  p φ f (fst a₀) (snd a₀))
        cases (inr x) = fst (fill {A = A} e α' p φ f (fst a₀) (snd a₀))
      agree : {i : Int} → prf (((i ≈O) ∨ (i ≈I) , left) ⌣ (φ , f))
      agree {i} u v = OI-elim-dep {B = λ u → left u ≡ f v} cases u where
        cases : (v₁ : (i ≡ O) ⊎ (i ≡ I)) → left ∣ v₁ ∣ ≡ f v
        cases (inl x) = symm (fst (snd (fill e α  p φ f (fst a₀) (snd a₀))) v)
        cases (inr x) = symm (fst (snd (fill e α' p φ f (fst a₀) (snd a₀))) v)
      joined : {i : Int} → [ ((i ≈O) ∨ (i ≈I)) ∨ φ ] → Π (A ∘ p)
      joined {i} = _∪_ {φ = (i ≈O) ∨ (i ≈I)} {ψ = φ} left f {p = agree}
      a₀' : {i : Int} → set (A (p ⟨ e ⟩)) (_↗_ ((((i ≈O) ∨ (i ≈I)) ∨ φ , left ∪ f) ∙ ⟨ e ⟩))
      fst (a₀' {i}) = fst a₀
      snd (a₀' {i}) u = or-elim-eq (λ u → joined u ⟨ e ⟩) (fst a₀) (λ {l} → leftCase {l}) (λ {r} → snd a₀ r) u where
        leftCase : {l : [ (i ≈O) ∨ (i ≈I) ]} → joined ∣ inl l ∣ ⟨ e ⟩ ≡ fst a₀
        leftCase {l} = OI-elim-dep {B = λ u → joined ∣ inl u ∣ ⟨ e ⟩ ≡ fst a₀} cases l where
          cases : (v : (i ≡ O) ⊎ (i ≡ I)) → joined ∣ inl ∣ v ∣ ∣ ⟨ e ⟩ ≡ fst a₀
          cases (inl x) = snd (snd (fill e α  p φ f (fst a₀) (snd a₀)))
          cases (inr x) = snd (snd (fill e α' p φ f (fst a₀) (snd a₀)))
      a₁ : (i : Int) → set (A (p ⟨ ! e ⟩)) (_↗_ ((((i ≈O) ∨ (i ≈I)) ∨ φ , joined) ∙ ⟨ ! e ⟩))
      a₁ i = α e p (((i ≈O) ∨ (i ≈I)) ∨ φ) joined a₀'
      a₁' : (i : Int) → set (A (p ⟨ ! e ⟩)) (_↗_ ((φ , f) ∙ ⟨ ! e ⟩))
      a₁' i = fst (a₁ i) , (λ u → snd (a₁ i) ∣ inr u ∣)
      atZero : a₁' O ≡ α e p φ f a₀
      atZero = incMono ((_↗_ ((φ , f) ∙ ⟨ ! e ⟩))) (a₁' O) (α e p φ f a₀)
        (proof:
           fst (a₁ O)
          ≡[ symm (snd (a₁ O) ∣ inl ∣ inl refl ∣ ∣) ]≡
           fst (fill e α p φ f (fst a₀) (snd a₀)) ⟨ ! e ⟩
          ≡[ fillAtEnd e α p φ f (fst a₀) (snd a₀) ]≡
           fst (α e p φ f a₀)
         qed)
      atOne : a₁' I ≡ α' e p φ f a₀
      atOne = incMono ((_↗_ ((φ , f) ∙ ⟨ ! e ⟩))) (a₁' I) (α' e p φ f a₀)
        (proof:
           fst (a₁ I)
          ≡[ symm (snd (a₁ I) ∣ inl ∣ inr refl ∣ ∣) ]≡
           fst (fill e α' p φ f (fst a₀) (snd a₀)) ⟨ ! e ⟩
          ≡[ fillAtEnd e α' p φ f (fst a₀) (snd a₀) ]≡
           fst (α' e p φ f a₀)
         qed)

propPairEq : {A : Set}{α : Fib {Γ = Unit} (λ tt → A)}{B : A → Set}{β : Fib B}{isprop : (a : A) → isProp (B a)}{a a' : A}{b : B a}{b' : B a'} → a ~ a' → (a , b) ~ (a' , b')
fst (propPairEq {A} {α} {B} {β} {isprop} {b = b} {b'} p) i =
  fst (αβ I' (λ _ → tt) (i ≈O ∨ i ≈I) (OI-elim f) {!!}) where
    αβ : Fib (Σ' (λ _ → A) (B ∘ snd))
    αβ = FibΣ {Γ = Unit} {A = λ _ → A} {B = B ∘ snd} α (λ e p → β e (snd ∘ p))
    f : {i : Int} → (i ≡ O) ⊎ (i ≡ I) → Int → Σ A B
    f (inl refl) j = (fst p j , fst (β O' (λ k → fst p (min j k)) cofFalse (λ ()) (subst B (symm (fst (snd p))) b , (λ ()))))
    f (inr refl) j = (fst p I , fst ((isprop (fst p I)) (fst (β O' (fst p) cofFalse (λ ()) (subst B (symm (fst (snd p))) b , (λ ())))) (subst B (symm (snd (snd p))) b')) j)
snd (propPairEq p) = {!!}

_~'_ : {l : Level}{A : Set l}(a a' : A) → Set l
_~'_ {A = A} a a' = Σ p ∈ (Int → A) , (p O ≡ a) × (p I ≡ a')

pathInv' : {A B : Set}(P : IdU A B)(ρ : Fib (fst P)) → _~'_ {A = Σ P ∈ (Int → Set) , Fib P} (fst P , ρ) (fst (fst (pathToPath P ρ)) , snd (pathToPath P ρ))
pathInv' P ρ = {!propPairEq ?!}
-- fst (fst (pathInv' P ρ) i) = let rr = pathInv P ρ i in (fst rr , (let kk = fst (snd rr) in trans (let uu = fst (snd P) in {!!}) kk ) , {!!})
-- snd (fst (pathInv' P ρ) i) e p φ f x = {!!}
-- snd (pathInv' P ρ) = {!!}
