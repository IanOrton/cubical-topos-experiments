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
module replace where 

open import Agda.Builtin.TrustMe
open import prelude
open import impredicative
open import interval
open import cof
open import fibrations


----------------------------------------------------------------------
-- Lemmas about subst
----------------------------------------------------------------------
substcancel :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  (B : A → Set ℓ')
  {x y : A}
  (f : (a : A) → B a)
  (p : x ≡ y)
  {z : A}
  (q : x ≡ z)
  (r : y ≡ z)
  → ------------------------
  subst B q (f x) ≡ subst B r (f y)
substcancel _ _ refl refl refl = refl

substtrans :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  (B : A → Set ℓ')
  {x y z : A}
  (p : x ≡ y)
  (q : y ≡ z)
  (r : x ≡ z)
  (b : B x)
  → ------------------------
  subst B q (subst B p b)  ≡ subst B r b
substtrans _ refl refl refl _ = refl

substcong :
  {ℓ ℓ' : Level}
  {A A' : Set ℓ}
  (B : A' → Set ℓ')
  (f : A → A')
  {x y : A}
  (p : x ≡ y)
  (b : B (f x))
  → ------------------------
  subst (B ∘ f) p b ≡ subst B (cong f p) b
substcong _ _ refl _ = refl

----------------------------------------------------------------------
-- Quoitents
----------------------------------------------------------------------
infix 6 _/_ [_]/_
postulate
  -- quotient formation
  _/_ : {ℓ ℓ' : Level}(A : Set ℓ)(R : A → A → Set ℓ') → Set (ℓ ⊔ ℓ')
  
  -- quotient introduction
  [_]/_ : {ℓ ℓ' : Level}{A : Set ℓ} → A → (R : A → A → Set ℓ') → A / R

  -- generating equalities
  qeq :
    {ℓ ℓ' : Level}
    {A : Set ℓ}
    {x y : A}
    (R : A → A → Set ℓ')
    (r : R x y)
    → ------------------
    [ x ]/ R ≡ [ y ]/ R

  -- quotient induction
  qind :
    {ℓ ℓ' ℓ'' : Level}
    {A : Set ℓ}
    (R : A → A → Set ℓ')
    (B : A / R → Set ℓ'')
    (f : (x : A) → B ([ x ]/ R))
    (e : (x y : A)(r : R x y) → subst B (qeq R r) (f x) ≡ f y)
    → --------------------------------------------------------
    (y : A / R) → B y

  -- quotient computation
  qind-comp :
    {ℓ ℓ' ℓ'' : Level}
    {A : Set ℓ}
    (R : A → A → Set ℓ')
    (B : A / R → Set ℓ'')
    (f : (x : A) → B ([ x ]/ R))
    (e : (x y : A)(r : R x y) → subst B (qeq R r) (f x) ≡ f y)
    (x : A)
    → --------------------------------------------------------
    qind R B f e ([ x ]/ R) ≡ f x

{-# REWRITE qind-comp   #-}

-- N.B. Not sure if these are correct:
{-# POLARITY _/_ * * ++ ++ #-}
{-# POLARITY [_]/_ * * _ * _ #-}

----------------------------------------------------------------------
-- Fibrant replacement of an object
----------------------------------------------------------------------
isFibObj : Set → Set
isFibObj A = isFib {Γ = Unit} (λ _ → A)

mutual
  -- FreeComps A is the result of freely adding compositions to A
  data FreeComps (A : Set) : Set where
    pure : A → FreeComps A
    comp :
      (e : OI)
      (φ : Cof)
      (f : [ φ ] → Int → Replace A)
      (a₀ : ⟦ a₀ ∈ Replace A ∣ (φ , f) ∙ ⟨ e ⟩ ↗ a₀ ⟧)
      → FreeComps A

  -- Replace A is FreeComps A where we quotient by the equation:
  --     comp e cofTrue f a₀ = f tt
  -- i.e. we ensure that compositions always extend their partial input
  Replace : Set → Set
  Replace A = FreeComps A / TotalComps

  -- TotalComps is the inductive family describing the necessary relation
  data TotalComps {A : Set} : FreeComps A → FreeComps A → Set where
    total :
      (e : OI)
      (φ : Cof)
      (f : [ φ ] → Int → Replace A)
      (a₀ : ⟦ a₀ ∈ Replace A ∣ (φ , f) ∙ ⟨ e ⟩ ↗ a₀ ⟧)
      (u : [ φ ])
      (a : FreeComps A)
      (_ : [ a ]/ TotalComps ≡ f u ⟨ ! e ⟩)
      → TotalComps a (comp e φ f a₀)

-- The inclusion of A in Replace A
ι : {A : Set} → A → Replace A
ι a = [ pure a ]/ TotalComps

-- Replace A is always a fibrant object
replaceIsFib : (A : Set) → isFibObj (Replace A)
replaceIsFib A e p φ f a₀ = [ comp e φ f a₀ ]/ TotalComps , ext where
  ext : (u : [ φ ]) → f u ⟨ ! e ⟩ ≡ [ comp e φ f a₀ ]/ TotalComps
  ext u = qind TotalComps
    (λ a → (_ : a ≡ f u ⟨ ! e ⟩) → a ≡ [ comp e φ f a₀ ]/ TotalComps)
    (λ a p → qeq TotalComps (total e φ f a₀ u a p))
    (λ _ _ _ → funext (λ _ → uip _ _))
    (f u ⟨ ! e ⟩) refl

-- We get a principle for eliminating into fibrant objects
replaceElim :
  (A : Set)
  (B : Set)(β : isFibObj B)
  (f : A → B)
  → --------------------
  Replace A → B

-- We need to mark this as terminating, but this should (hopefully) be ok
{-# TERMINATING #-}
replaceElim A B β f = elim where
  elim : Replace A → B
  f' : (x : FreeComps A) → B
  resp : (x y : FreeComps A) (r : TotalComps x y) → subst (λ _ → B) (qeq TotalComps r) (f' x) ≡ f' y
  elim = qind TotalComps (λ _ → B) f' resp
  f' (pure x) = f x
  f' (comp e φ g (a₀ , ext)) = fst (β e (λ _ → tt) φ (λ u i → elim (g u i))
    (elim a₀ , λ u → cong (qind TotalComps (λ _ → B) f' resp) (ext u)))
  resp a .(comp e φ g (a₀ , ext)) (total e φ g (a₀ , ext) u .a eq) =
    proof:
      subst (λ _ → B) (qeq TotalComps (total e φ g (a₀ , ext) u a eq)) (f' a)
        ≡[ substconst _ (qeq TotalComps (total e φ g (a₀ , ext) u a eq)) (f' a) ]≡
      f' a
        ≡[ cong elim eq ]≡
      elim (g u ⟨ ! e ⟩)
        ≡[ snd (β e (λ _ → tt) φ (λ u i → elim (g u i))
             (elim a₀ , λ u → cong (qind TotalComps (λ _ → B) f' resp) (ext u))) u ]≡
      fst (β e (λ _ → tt) φ (λ u i → elim (g u i))
        (elim a₀ , λ u → cong (qind TotalComps (λ _ → B) f' resp) (ext u)))
        ≡[ refl ]≡
      f' (comp e φ g (a₀ , ext))
    qed

-- Every f : A --> B factors as (replaceElim f) ∘ ι
--
--  A --------> B
--   \         ➚
--    \       /
--     \    /
--      ➘ /
--   Replace A
--
replaceElimFactors :
  (A : Set)
  (B : Set)(β : isFibObj B)
  (f : A → B)
  → ---------------
  (replaceElim A B β f) ∘ ι ≡ f
replaceElimFactors A B β f = refl 


-- A corresponding induction principle
replaceInd :
  (A : Set)
  (B : Replace A → Set)(β : isFib B)
  (f : (a : A) → B (ι a))
  → --------------------
  (x : Replace A) → B x
{-# TERMINATING #-}
replaceInd A B β f = elim where
  elim : (x : Replace A) → B x
  f' : (x : FreeComps A) → B ([ x ]/ TotalComps)
  resp : (x y : FreeComps A) (r : TotalComps x y) → subst B (qeq TotalComps r) (f' x) ≡ f' y
  elim = qind TotalComps B f' resp
  f' (pure x) = f x
  f' (comp e φ g (a₀ , ext)) =
    let p = fill e (replaceIsFib A) (λ _ → tt) φ g a₀ ext in
    let g' u i = subst B (appCong (fst (snd p) u)) (elim (g u i)) in
    let a₀' = subst B (symm (snd (snd p))) (elim a₀) in
    let ext' u = substcancel B elim (ext u) (appCong (fst (snd p) u)) (symm (snd (snd p))) in
    let a₁' = fst (β e (fst p) φ g' (a₀' , ext')) in
    subst B (fillAtEnd e (replaceIsFib A) (λ _ → tt) φ g a₀ ext) a₁'
  resp a .(comp e φ g (a₀ , ext)) (total e φ g (a₀ , ext) u .a eq) =
    let p = fill e (replaceIsFib A) (λ _ → tt) φ g a₀ ext in
    let g' u i = subst B (appCong (fst (snd p) u)) (elim (g u i)) in
    let a₀' = subst B (symm (snd (snd p))) (elim a₀) in
    let ext' u = substcancel B elim (ext u) (appCong (fst (snd p) u)) (symm (snd (snd p))) in
    let a₁' = fst (β e (fst p) φ g' (a₀' , ext')) in
    proof:

      subst B (qeq TotalComps (total e φ g (a₀ , ext) u a eq)) (f' a)

          ≡[ substcancel B elim eq
               (qeq TotalComps (total e φ g (a₀ , ext) u a eq))
               (snd (replaceIsFib A e (λ _ → tt) φ g (a₀ , ext)) u) ]≡

      subst B (snd (replaceIsFib A e (λ _ → tt) φ g (a₀ , ext)) u) (elim (g u ⟨ ! e ⟩))

          ≡[ symm (substtrans B
                    (appCong (fst (snd p) u))
                    (fillAtEnd e (replaceIsFib A) (λ _ → tt) φ g a₀ ext)
                    (snd (replaceIsFib A e (λ _ → tt) φ g (a₀ , ext)) u)
                    (elim (g u ⟨ ! e ⟩))) ]≡

      subst B (fillAtEnd e (replaceIsFib A) (λ _ → tt) φ g a₀ ext) (g' u ⟨ ! e ⟩)
   
          ≡[ cong (subst B (fillAtEnd e (replaceIsFib A) (λ _ → tt) φ g a₀ ext))
                  (snd (β e (fst p) φ g' (a₀' , ext')) u) ]≡

      subst B (fillAtEnd e (replaceIsFib A) (λ _ → tt) φ g a₀ ext) a₁'

          ≡[ refl ]≡

      f' (comp e φ g (a₀ , ext))

    qed


-- And a corresponding factorisation lemma
replaceIndFactors : (A : Set)(B : Replace A → Set)(β : isFib B)(f : (a : A) → B (ι a))
  → (λ a → replaceInd A B β f (ι a)) ≡ f
replaceIndFactors A B β f = refl 

----------------------
-- 𝕊¹
----------------------
open import Data.paths

data Endpoints : Int → Int → Set where
  I=O : Endpoints I O

pre𝕊¹ : Set
pre𝕊¹ = Int / Endpoints

𝕊¹ : Set
𝕊¹ = Replace pre𝕊¹

𝕊¹fib : isFibObj 𝕊¹
𝕊¹fib = replaceIsFib pre𝕊¹

base : 𝕊¹
base = ι ([ O ]/ Endpoints)

loop : base ~ base
loop = p , refl , cong ι (qeq Endpoints I=O) where
  p : Int → 𝕊¹
  p i = ι ([ i ]/ Endpoints)

𝕊¹-elim :
  (P : 𝕊¹ → Set)
  (ρ : isFib P)
  (a : P base)
  (l : (i : Int) → P (loop at i))
  (lO : subst P (atO loop) (l O) ≡ a)
  (lI : subst P (atI loop) (l I) ≡ a)
  → ---------------------
  (x : 𝕊¹) → P x
𝕊¹-elim P ρ a l lO lI x = replaceInd pre𝕊¹ P ρ f x where
  f : (x : pre𝕊¹) → P (ι x)
  f = qind Endpoints (P ∘ ι) l resp where
    resp : (i j : Int) (r : Endpoints i j) →
      subst (P ∘ ι) (qeq Endpoints r) (l i) ≡ l j
    resp .I .O I=O =
      proof:
        subst (P ∘ ι) (qeq Endpoints I=O) (l I)
          ≡[ substcong P ι (qeq Endpoints I=O) (l I) ]≡
        subst P (cong ι (qeq Endpoints I=O)) (l I)
          ≡[ lI ]≡
        a
          ≡[ symm lO ]≡
        l O
      qed

-----------------------------
-- Suspension (of an object)
-----------------------------
data preSusp (X : Set) : Set where
  preNorth : preSusp X
  preSouth : preSusp X
  preMerid : X → Int → preSusp X

data MeridEnds {X : Set} : preSusp X → preSusp X → Set where
  meridO : (x : X) → MeridEnds (preMerid x O) preNorth
  meridI : (x : X) → MeridEnds (preMerid x I) preSouth

Susp : Set → Set
Susp X = Replace (preSusp X / MeridEnds)

north : {X : Set} → Susp X
north = ι ([ preNorth ]/ MeridEnds)

south : {X : Set} → Susp X
south = ι ([ preSouth ]/ MeridEnds)

merid : {X : Set} → X → north ~ south
merid {X} x = p , (cong ι (qeq MeridEnds (meridO x))) , cong ι (qeq MeridEnds (meridI x)) where
  p : Int → Susp X
  p i = ι ([ preMerid x i ]/ MeridEnds)

Susp-elim :
  (X  : Set)
  (P  : Susp X → Set)
  (ρ  : isFib P)
  (an : P north)
  (as : P south)
  (al : (x : X)(i : Int) → P (merid x at i))
  (lO : (x : X) → subst P (atO (merid x)) (al x O) ≡ an)
  (lI : (x : X) → subst P (atI (merid x)) (al x I) ≡ as)
  → ---------------------
  (x : Susp X) → P x
Susp-elim X P ρ an as al lO lI = replaceInd _ P ρ f where
  f : (x : preSusp X / MeridEnds) → P (ι x)
  f = qind MeridEnds (P ∘ ι) f' resp where
    f' : (x : preSusp X) → (P ∘ ι) ([ x ]/ MeridEnds)
    f' preNorth = an
    f' preSouth = as
    f' (preMerid x i) = al x i
    resp : (x y : preSusp X) (r : MeridEnds x y) →
      subst (P ∘ ι) (qeq MeridEnds r) (f' x) ≡ f' y
    resp .(preMerid x O) .preNorth (meridO x) =
      proof:
        subst (P ∘ ι) (qeq MeridEnds (meridO x)) (al x O)
          ≡[ substcong P ι (qeq MeridEnds (meridO x)) (al x O) ]≡
        subst P (cong ι (qeq MeridEnds (meridO x))) (al x O)
          ≡[ lO x ]≡
        an
      qed
    resp .(preMerid x I) .preSouth (meridI x) =
      proof:
        subst (P ∘ ι) (qeq MeridEnds (meridI x)) (al x I)
          ≡[ substcong P ι (qeq MeridEnds (meridI x)) (al x I) ]≡
        subst P (cong ι (qeq MeridEnds (meridI x))) (al x I)
          ≡[ lI x ]≡
        as
      qed

SuspFunctorial : 
  (X Y : Set)
  (f : X → Y)
  → ---------------------
  Susp X → Susp Y
SuspFunctorial X Y f =
  Susp-elim X (λ _ → Susp Y) (reindex (λ _ → Susp Y) (replaceIsFib (preSusp Y / MeridEnds)) (λ _ → tt))
    north  -- north ↦ north
    south  -- south ↦ south
    (λ x i → (merid (f x)) at i)  -- merid x ↦ merid (f x)
    (λ x → proof:
      subst (λ _ → Susp Y) (atO (merid x)) (merid (f x) at O)
        ≡[ substconst (Susp Y) (atO (merid x)) (merid (f x) at O) ]≡
      merid (f x) at O
        ≡[ atO (merid (f x)) ]≡
      north
    qed)
    (λ x → proof:
      subst (λ _ → Susp Y) (atI (merid x)) (merid (f x) at I)
        ≡[ substconst (Susp Y) (atI (merid x)) (merid (f x) at I) ]≡
      merid (f x) at I
        ≡[ atI (merid (f x)) ]≡
      south
    qed)

 
