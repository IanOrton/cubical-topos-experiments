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
module cof where 

open import prelude
open import impredicative
open import interval

infixr 4 _∨_
infix  5 _↗_
infix  6 _∙_

----------------------------------------------------------------------
-- Cofibrant propositions
----------------------------------------------------------------------
postulate
 cof   : Ω → Ω
 cofO  : (i : Int) → prf (cof (i ≈ O))
 cofI  : (i : Int) → prf (cof (i ≈ I))
 cofor : (P Q : Ω) → prf (cof P ⊃ cof Q ⊃ cof(P or Q))
 cof&  : (P Q : Ω) → prf (cof P ⊃ (P ⊃ cof Q) ⊃ cof(P & Q))
 cof∀  : (P : Int → Ω) → prf ((All i ∈ Int , cof (P i)) ⊃ cof (All i ∈ Int , P i))
 
Cof : Set
Cof = ⟦ P ∈ Ω ∣ cof P ⟧

[_] : Cof → Set
[ φ ] = prf (fst φ)

cofFalse : Cof
fst cofFalse = ⊥
snd cofFalse = subst (prf ∘ cof) (propext O≠I ∅-elim) (cofI O)

cofTrue : Cof
fst cofTrue = ⊤
snd cofTrue = subst (prf ∘ cof) (propext (λ _ → tt) (λ _ → refl)) (cofO O)

_≈O : (i : Int) → Cof
fst (i ≈O) = i ≈ O
snd (i ≈O) = cofO i

_≈I : (i : Int) → Cof
fst (i ≈I) = i ≈ I
snd (i ≈I) = cofI i

_≈OI_ : (i : Int)(e : OI) → Cof
fst (i ≈OI e) = i ≈ ⟨ e ⟩
snd (i ≈OI e) with e
... | O' = cofO i
... | I' = cofI i

_∨_ : Cof → Cof → Cof
(P , u) ∨ (Q , v) = ((P or Q) , cofor P Q u v)

_∧_ : Cof → Cof → Cof
(P , u) ∧ (Q , v) = ((P & Q) , cof& P Q u (λ _ → v))

cofEq : {P Q : Cof} → fst P ≡ fst Q → P ≡ Q
cofEq {P , cofP} {.P , cofP'} refl = cong (_,_ P) (equ (cof P) cofP cofP' )

----------------------------------------------------------------------
-- Cofibrant-partial function classifier
----------------------------------------------------------------------
□ : Set → Set
□ A = Σ φ ∈ Cof , ([ φ ] → A)

_↗_ : {A : Set} → □ A → A → Ω
(φ , f) ↗ x = All u ∈ [ φ ] , f u ≈ x

----------------------------------------------------------------------
-- Dependently typed paths
----------------------------------------------------------------------
Π : (Int → Set) → Set
Π A = (i : Int) → A i

Π′ :
  {A B : Int → Set}
  → ---------------------------------
  ((i : Int) → A i → B i) → Π A → Π B
Π′ F p i = F i (p i)

_∙_ :
  {A : Int → Set}
  → -------------------------
  □(Π A) → (i : Int) → □(A i)
(φ , f) ∙ i = (φ , λ u → f u i)

