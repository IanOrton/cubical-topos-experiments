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
module contract where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import equivs
open import Data.paths

----------------------------------------------------------------------
-- Contraction type
----------------------------------------------------------------------
Contract :
  {Γ : Set}
  (A : Γ → Set)
  → ---------------
  Γ × Int → Set
Contract A (x , i) = [ i ≈O ] → A x

-- Isomorphic to A at O
ContractO :
  {Γ : Set}
  (A : Γ → Set)
  → ---------------
  (Contract A ∘ (λ x → (x , O))) ≅ A
ContractO A x = f , g , funext (λ _ → funext (λ{ refl → refl})) , refl where
  f : Contract A (x , O) → A x
  f a? = a? refl
  g : A x → Contract A (x , O)
  g a _ = a

-- Isomorphic to Unit at I
ContractI :
  {Γ : Set}
  (A : Γ → Set)
  → ---------------
  (Contract A ∘ (λ x → (x , I))) ≅ (λ _ → Unit)
ContractI A x = f , g , funext (λ _ → funext (λ I≡O → cdiction I≡O)) , funext λ{ tt → refl } where
  f : Contract A (x , I) → Unit
  f _ = tt
  cdiction : {A : Set} → I ≡ O → A
  cdiction I≡O = ∅-elim (O≠I (symm I≡O))
  g : Unit → Contract A (x , I)
  g tt = cdiction

-- Contract A is fibrant
-- FibContract' :
--   {Γ : Set}
--   (A : Γ → Set)
--   → ---------------
--   Fib A → Fib (Contract A)
-- FibContract' {Γ} A α e p φ f contr = ((λ u → fst (a u)) , a-extends-f) where

--   -- The Γ component of the end of the path p
--   x!e : Γ
--   x!e = fst (p ⟨ ! e ⟩)
  
--   -- The centre of contraction above x!e
--   a₀ : A x!e
--   a₀ = fst (contr x!e)
  
--   -- When f is defined we get a path from a₀ to f !e
--   -- since a₀ is the centre of contraction
--   a₀~f!e :
--     (p!e≡O : snd (p ⟨ ! e ⟩) ≡ O)
--     (u : [ φ ]) -- f is defined
--     → -----------
--     a₀ ~ f u ⟨ ! e ⟩ p!e≡O
--   a₀~f!e p!e≡O u = snd (contr x!e) (f u ⟨ ! e ⟩ p!e≡O)
  
--   -- The final result is obtained by composing from a₀ along
--   -- the (partial) path to f !e, which we defined above
--   a :
--     (p!e≡O : snd (p ⟨ ! e ⟩) ≡ O)
--     → -----------
--     ⟦ a ∈ A x!e ∣ (φ , (λ u → fst (a₀~f!e p!e≡O u) I)) ↗ a ⟧
--   a p!e≡O =
--     α O' (λ _ → x!e) φ
--       (λ u → fst (a₀~f!e p!e≡O u))              -- along a₀~f!e
--       (a₀ , (λ u → fst (snd (a₀~f!e p!e≡O u)))) -- from a₀

--   -- Finally we must show that f agrees with a when it is defined
--   a-extends-f : (u : [ φ ]) → f u ⟨ ! e ⟩ ≡ (λ u → fst (a u))
--   a-extends-f u = funext (λ p!e≡O → trans (snd (a p!e≡O) u) (symm (snd (snd (a₀~f!e p!e≡O u)))))

-- If A is fibrant then so is Contract A
FibContract :
  {Γ : Set}
  (A : Γ → Set)
  (contr : (x : Γ) → (Contr (A x)))
  → ---------------
  Fib A → Fib (Contract A)
FibContract {Γ} A contr α e p φ f _ = ((λ u → fst (a u)) , a-extends-f) where

  -- The Γ component of the end of the path p
  x!e : Γ
  x!e = fst (p ⟨ ! e ⟩)
  
  -- The centre of contraction above x!e
  a₀ : A x!e
  a₀ = fst (contr x!e)
  
  -- When f is defined we get a path from a₀ to f !e
  -- since a₀ is the centre of contraction
  a₀~f!e :
    (p!e≡O : snd (p ⟨ ! e ⟩) ≡ O)
    (u : [ φ ]) -- f is defined
    → -----------
    a₀ ~ f u ⟨ ! e ⟩ p!e≡O
  a₀~f!e p!e≡O u = snd (contr x!e) (f u ⟨ ! e ⟩ p!e≡O)
  
  -- The final result is obtained by composing from a₀ along
  -- the (partial) path to f !e, which we defined above
  a :
    (p!e≡O : snd (p ⟨ ! e ⟩) ≡ O)
    → -----------
    ⟦ a ∈ A x!e ∣ (φ , (λ u → fst (a₀~f!e p!e≡O u) I)) ↗ a ⟧
  a p!e≡O =
    α O' (λ _ → x!e) φ
      (λ u → fst (a₀~f!e p!e≡O u))              -- along a₀~f!e
      (a₀ , (λ u → fst (snd (a₀~f!e p!e≡O u)))) -- from a₀

  -- Finally we must show that f agrees with a when it is defined
  a-extends-f : (u : [ φ ]) → f u ⟨ ! e ⟩ ≡ (λ u → fst (a u))
  a-extends-f u = funext (λ p!e≡O → trans (snd (a p!e≡O) u) (symm (snd (snd (a₀~f!e p!e≡O u)))))


-- Might be needed to show that the fibration structure on
-- Contract A restricts to the original one given for A
postulate
  cof∀  : (P : Int → Ω) → prf ((All i ∈ Int , cof (P i)) ⊃ cof (All i ∈ Int , P i))

_∀≈O : (i : Int → Int) → Cof
fst (p ∀≈O) = All i ∈ Int , p i ≈ O
snd (p ∀≈O) = cof∀ (λ i → p i ≈ O) (λ i → cofO (p i))


--  (α : Fib A) → (e : OI)(p : Int → Γ × Int)(φ : Cof)(f : [ φ ] → Π (Contract A ∘ p))
  --        (a₀ : ⟦ x₁ ∈ (Contract A (p ⟨ e ⟩)) ∣ (φ , f) ∙ ⟨ e ⟩ ↗ x₁ ⟧)
    --      → Σ a₁ ∈ ⟦ x₁ ∈ (Contract A (p ⟨ ! e ⟩)) ∣ (φ , f) ∙ ⟨ ! e ⟩ ↗ x₁ ⟧ , {!? → a₁ ≡ α e ? φ ? ?!}

-- If A is fibrant then so is Contract A
FibContract' :
  {Γ : Set}
  (A : Γ → Set)
  (contr : (x : Γ) → (Contr (A x)))
  → ---------------
  Fib A → Fib (Contract A)
FibContract' {Γ} A contr α e p φ f (a? , ext) = ((λ u → fst (a u)) , a-extends-f) where

  -- The Γ component of the end of the path p
  x!e : Γ
  x!e = fst (p ⟨ ! e ⟩)
  
  -- The centre of contraction above x!e
  a₀ : A x!e
  a₀ = fst (contr x!e)
  
  -- When f is defined we get a path from a₀ to f !e
  -- since a₀ is the centre of contraction
  a₀~f!e :
    (p!e≡O : snd (p ⟨ ! e ⟩) ≡ O)
    (u : [ φ ]) -- f is defined
    → -----------
    a₀ ~ f u ⟨ ! e ⟩ p!e≡O
  a₀~f!e p!e≡O u = snd (contr x!e) (f u ⟨ ! e ⟩ p!e≡O)

  -- If the path is constantly zero in its second component
  -- then we can use the filling in A
  g : (pi≡O : (x : Int) → (snd ∘ p) x ≡ O) → ⟦ a ∈ A x!e ∣ (φ , (λ u → f u ⟨ ! e ⟩ (pi≡O ⟨ ! e ⟩))) ↗ a ⟧
  g pi≡O = α e (fst ∘ p) φ (λ u i → f u i (pi≡O i)) (a? (pi≡O ⟨ e ⟩) , (λ u → cong (λ f → f (pi≡O ⟨ e ⟩)) (ext u)))
  a₀~g :
    (pi≡O : (x : Int) → (snd ∘ p) x ≡ O)
    → -----------
    a₀ ~ fst (g pi≡O)
  a₀~g pi≡O = snd (contr x!e) (fst (g pi≡O))
  
  -- The final result is obtained by composing from a₀ along
  -- the (partial) path to f !e, which we defined above
  f' : (p!e≡O : snd (p ⟨ ! e ⟩) ≡ O) → [ φ ∨ ((snd ∘ p) ∀≈O) ] → Π (A ∘ (λ _ → x!e))
  f' p!e≡O u = _∪_ {φ = φ} {ψ = (snd ∘ p) ∀≈O}
        (λ u → fst (a₀~f!e p!e≡O u))
        (λ pi≡O → fst (a₀~g pi≡O))
        {p = λ u pi≡O →
          cong (λ x → fst (snd (contr x!e) x))
            (trans (snd (g pi≡O) u) (cong (f u ⟨ ! e ⟩) (eq (snd (p ⟨ ! e ⟩) ≈ O))))}
        u
  a :
    (p!e≡O : snd (p ⟨ ! e ⟩) ≡ O)
    → -----------
    ⟦ a ∈ A x!e ∣ (φ ∨ ((snd ∘ p) ∀≈O) , (λ u → f' p!e≡O u I)) ↗ a ⟧
  a p!e≡O =
    α O' (λ _ → x!e) (φ ∨ (snd ∘ p) ∀≈O)
      (f' p!e≡O)
      (a₀ , or-elim-eq (λ u → f' p!e≡O u O) a₀
        (λ {l} → fst (snd (snd (contr (fst (p ⟨ ! e ⟩))) (f l ⟨ ! e ⟩ p!e≡O))))
        (λ {r} → fst (snd (snd (contr (fst (p ⟨ ! e ⟩))) (fst (g r))))))


  -- Finally we must show that f agrees with a when it is defined
  a-extends-f : (u : [ φ ]) → f u ⟨ ! e ⟩ ≡ (λ u → fst (a u))
  a-extends-f u = funext (λ p!e≡O → trans (snd (a p!e≡O) ∣ inl u ∣) (symm (snd (snd (a₀~f!e p!e≡O u)))))

FibContractO :
  {Γ : Set}
  (A : Γ → Set)
  (contr : (x : Γ) → (Contr (A x)))
  (α : Fib A)
  → ---------------
  let α-contract   = FibContract' A contr α in
  let α-contractO  = reindex (Contract A) α-contract (λ x → (x , O)) in
  let α-contractO' = FibIso ((Contract A) ∘ (λ x → (x , O))) A (ContractO A) α-contractO in 
  α-contractO' ≡ α
FibContractO {Γ} A contr α = fibExt {A = A} ptwise where
  ptwise : (e : OI) (p : Int → Γ) (φ : Cof)(f : [ φ ] → Π (A ∘ p))
      (a₀ : ⟦ x₁ ∈ (A (p ⟨ e ⟩)) ∣ (φ , f) ∙ ⟨ e ⟩ ↗ x₁ ⟧) →
      fst (FibIso (Contract A ∘ (λ x → x , O)) A (ContractO A)
       (reindex (Contract A) (FibContract' A contr α) (λ x → x , O)) e p φ f a₀)
      ≡ fst (α e p φ f a₀)
  ptwise e p φ f a₀ =
    let pi≡O : [ (λ i → O) ∀≈O ]
        pi≡O i = refl
    in {!!}
