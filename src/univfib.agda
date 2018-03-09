
{-# OPTIONS --rewriting #-}
open import Level
open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import equivs
open import glueing.strict

_^I : Set → Set
X ^I = Int → X

Sections : {Γ : Set} → (Γ → Set) → Set
Sections {Γ} A = (x : Γ) → A x

postulate
  -- The right adjoint
  R : {Γ : Set} → (Γ ^I → Set) → Γ → Set
  -- The adjunction
  adj : (X : Set)(Y : X ^I → Set) → Sections Y ≅' Sections (R Y)


isFib' : {Γ : Set} → (Γ → Set) → Γ → Set
isFib' A = R (λ p → (e : OI) → Comp e (A ∘ p))

postulate
  UFib  : Set₁
  ElFib : Fib UFib 

postulate
  -- The universe of small fibrations
  U : Set₁
  
  -- The family of elements,
  -- i.e. the generic fibration
  El : Fib U

  -- For converting fibrations
  -- to maps into U
  code :
    {Γ : Set₁}
    (A : Fib Γ)
    → --------------
    Γ → U

  -- Reindexing along a code gives
  -- the original fibration
  code-el :
    {Γ : Set₁}
    (A : Fib Γ)
    → ----------------------
    reindex' El (code A) ≡ A



data Unit₁ : Set₁ where
  tt : Unit₁

FibFibers : {Γ : Set₁}(A : Γ → Set) → Set₁
FibFibers {Γ} A = ((x : Γ) → isFib {Γ = Unit₁} (λ _ → A x))

FamFib→FibFam :
  {Γ : Set₁}
  (A : Γ → Set)
  → ---------------
  FibFibers A → isFib A
FamFib→FibFam {Γ} A fib-fibers =
  let (A'' , α) = reindex' El a' in
  subst isFib eqFam α
    where
      a' : Γ → U
      a' x = code ((λ _ → A x) , fib-fibers x) tt
      eqFam : fst El ∘ a' ≡ A
      eqFam = funext
        (λ x → cong (λ fib → fst fib tt)
          (code-el ((λ _ → A x) , fib-fibers x)))

Int₁ : Set₁
Int₁ = Lift Int

P : Int₁ → Set
P i = (lower i ≡ O)

ffP : FibFibers P
ffP x e p φ f (i , ext) = i , (λ u → uip (f u ⟨ ! e ⟩) i)

fibP : isFib P
fibP = FamFib→FibFam P ffP

bad : I ≡ O
bad = fst (fibP O' lift cofFalse (λ ()) (refl , (λ ())))

very-bad : ∅
very-bad with O≠I (symm bad)
... | ()




-- postulate
  
--   -- From a map into the universe we can extract
--   -- a family and a fibration structure
--   toSet : {Γ : Set} → (Γ → U) → (Γ → Set)
--   toFib : {Γ : Set}(A : Γ → U) → isFib (toSet A)

--   -- Given a family and a fibration structure
--   -- we can construct a map into U
--   toU : {Γ : Set}(A : Γ → Set)(α : Fib A) → (Γ → U)

--   -- The toSet operation is stable under reindexing
--   toSetStable : {Δ Γ : Set}(A : Γ → U)(f : Δ → Γ) → (toSet A) ∘ f ≡ toSet (A ∘ f)

--   -- toSet is an inverse to toU
--   inv : {Γ : Set}(A : Γ → Set)(α : Fib A) → toSet (toU A α) ≡ A

-- toSetβ : {Γ : Set}(A : Γ → U)(x : Γ) → toSet A x ≡ toSet (λ _ → A x) tt
-- toSetβ A x = cong (λ f → f tt) (toSetStable A (λ _ → x))

-- FibFibers' : {Γ : Set₁}(A : Γ → Set) → Set₁
-- FibFibers' {Γ} A = ((x : Γ) → Fib {Γ = Unit} (λ _ → A x))

-- FamFib→FibFam :
--   {Γ : Set}
--   (A : Γ → Set)
--   → ---------------
--   FibFibers' A → Fib A
-- FamFib→FibFam {Γ} A fib-fibers = subst Fib eqFam α where
--   A' : Γ → U
--   A' x = toU (λ _ → A x) (fib-fibers x) tt
--   A'' : Γ → Set
--   A'' = toSet A'
--   α : Fib A''
--   α = toFib A'
--   eqFam : A'' ≡ A
--   eqFam = funext (λ x →
--     proof:
--       A'' x
--     ≡[ toSetβ A' x ]≡
--       toSet (λ _ → toU (λ _ → A x) (fib-fibers x) tt) tt
--     ≡[ cong (λ f → toSet f tt) (funext (λ{ tt → refl })) ]≡
--       toSet (toU (λ _ → A x) (fib-fibers x)) tt
--     ≡[ cong (λ f → f tt) (inv (λ _ → A x) (fib-fibers x)) ]≡
--       A x
--     qed)



-- -- UisFib' : Fib {Γ = Unit} (λ _ → U)
-- -- UisFib' e p φ Bfib (Afib , Aext) = toU (λ _ → G) γ tt , {!!} where
-- --   B : [ φ ] → Int → Set
-- --   B u = toSet (Bfib u)
-- --   β : (u : [ φ ]) → Fib (B u)
-- --   β u = toFib (Bfib u)

-- --   A : Set
-- --   A = toSet (λ _ → Afib) tt
-- --   α : (u : [ φ ]) → Fib (λ _ → A)
-- --   α u = toFib (λ _ → Afib)
  
-- --   f : (u : [ φ ]) → B u ⟨ ! e ⟩ → B u ⟨ e ⟩
-- --   f u b = fst (β u (! e) id cofFalse (λ ()) (b , (λ ())))
  
-- --   f' : (u : [ φ ]) → B u ⟨ ! e ⟩ → A
-- --   f' u b = coe (trans (cong (λ C → toSet (λ _ → C) tt) (Aext u)) (toSetβ (Bfib u) ⟨ e ⟩)) (f u b)

-- --   G : Set
-- --   G = (u : [ φ ]) →  B u ⟨ ! e ⟩

-- --   γ : Fib (λ _ → G)
-- --   γ e' p' φ' par (b , ext) = (b' , ext') where
-- --     b' : (u : [ φ ]) → B u ⟨ ! e ⟩
-- --     b' u = fst (β u e' (λ _ → ⟨ ! e ⟩) φ' (λ v i → par v i u) (b u , (λ v → cong (λ h → h u) (ext v))))

-- --     ext' : prf ((φ' , par) ∙ ⟨ ! e' ⟩ ↗ b')
-- --     ext' v = funext (λ u → snd (β u e' (λ _ → ⟨ ! e ⟩) φ' (λ v i → par v i u) (b u , (λ v → cong (λ h → h u) (ext v)))) v)

-- --   subst-lemma : {A : Set}{x : A}(p : x ≡ x){B : A → Set}{b : B x} → subst B p b ≡ b
-- --   subst-lemma refl = refl

-- --   extends : (u : [ φ ]) → B u ⟨ ! e ⟩ ≅' G
-- --   _≅'_.f (extends u) b u' = subst (λ u → B u ⟨ ! e ⟩) (eq (fst φ)) b
-- --   _≅'_.g (extends u) g = g u
-- --   _≅'_.inv₁ (extends u) = funext (λ b → subst-lemma (eq (fst φ)))
-- --   _≅'_.inv₂ (extends u) = funext (λ g → funext (λ u' → subst (λ u' →  subst (λ u₁ → toSet (Bfib u₁) ⟨ ! e ⟩) (equ (fst φ) u u') (g u) ≡ g u') (eq (fst φ)) (subst-lemma (eq (fst φ)))))

-- -- UisFib : Fib {Γ = Unit} (λ _ → U)
-- -- UisFib e p φ Bfib (Afib , Aext) = toU (λ _ → G) γ tt , {!!} where
-- --   B : [ φ ] → Int → Set
-- --   B u = toSet (Bfib u)
-- --   β : (u : [ φ ]) → Fib (B u)
-- --   β u = toFib (Bfib u)

-- --   A : Set
-- --   A = toSet (λ _ → Afib) tt
-- --   α : (u : [ φ ]) → Fib (λ _ → A)
-- --   α u = toFib (λ _ → Afib)
  
-- --   f : (u : [ φ ]) → B u ⟨ ! e ⟩ → B u ⟨ e ⟩
-- --   f u b = fst (β u (! e) id cofFalse (λ ()) (b , (λ ())))
  
-- --   f' : (u : [ φ ]) → B u ⟨ ! e ⟩ → A
-- --   f' u b = coe (trans (cong (λ C → toSet (λ _ → C) tt) (Aext u)) (toSetβ (Bfib u) ⟨ e ⟩)) (f u b)

-- --   G : Set
-- --   G = Σ b ∈ ((u : [ φ ]) →  B u ⟨ ! e ⟩) , ⟦ a ∈ A ∣ (φ , (λ u → f' u (b u))) ↗ a ⟧  -- SGlue {Γ = Unit} (λ _ → φ) (λ u → B (snd u) ⟨ ! e ⟩) (λ _ → A) f tt

-- --   γ : Fib (λ _ → G)
-- --   γ e' p' φ' par ((b , a , f'b=a) , ext) = ((b' , {!!} , {!!}) , {!!}) where
-- --     b' : (u : [ φ ]) → B u ⟨ ! e ⟩
-- --     b' u = fst (β u e' (λ _ → ⟨ ! e ⟩) φ' (λ v i → fst (par v i) u) (b u , (λ v → cong (λ h → fst h u) (ext v))))

-- --   --A↗G : prf ((φ , B) ∙ ⟨ ! e ⟩ ↗ G)
-- --   --A↗G u = symm (strictness {Γ = Unit} (λ _ → φ) (λ u → B (snd u) ⟨ ! e ⟩) (λ _ → A) f tt u)


-- -- -- UisFib' : Fib {Γ = Unit} (λ _ → Set)
-- -- -- UisFib' e p φ B (A , Aext) = G , A↗G where
-- -- --   f : (x : Unit) (u : [ φ ]) → B u ⟨ ! e ⟩ ≅' A
-- -- --   _≅'_.f (f x u) b = {!!}
-- -- --   _≅'_.g (f x u) x₁ = {!!}
-- -- --   _≅'_.inv₁ (f x u) = {!!}
-- -- --   _≅'_.inv₂ (f x u) = {!!}

-- -- --   G : Set
-- -- --   G = strictify {Γ = Unit} (λ _ → φ) (λ u → B (snd u) ⟨ ! e ⟩) (λ _ → A) f tt

-- -- --   A↗G : prf ((φ , B) ∙ ⟨ ! e ⟩ ↗ G)
-- -- --   A↗G u = restrictsToA {Γ = Unit} (λ _ → φ) (λ u → B (snd u) ⟨ ! e ⟩) (λ _ → A) f (tt , u)
