----------------------------------------------------------------------
-- This Agda code is an experiment with building universes internally
--
-- The idea for getting an impredicative universe of propositions Ω
-- comes from Martin Escardo, more details can be found at:
--
--          http://www.cs.bham.ac.uk/~mhe/impredicativity/
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module Data.universe where

open import prelude
open import impredicative
open import cof
open import interval
open import fibrations
open import equivs
open import Data.products
open import Data.functions
open import Data.paths

----------------------------------------------------------------------
-- Postulates for the universe
----------------------------------------------------------------------
postulate
  U  :{♭} Set₁
  El :{♭} U → Set
  el :{♭} isFib El
  code : {a :{♭} Level}{Γ :{♭} Set a}(A :{♭} Fib Γ) → (Γ → U)

decode : ∀{a}{Γ : Set a} → (Γ → U) → Fib Γ
decode = reindex' (El , el)

postulate
  code-el  : {a :{♭} Level}{Γ :{♭} Set a}(A :{♭} Fib Γ) → decode (code A) ≡ A
  code-el' : {a :{♭} Level}{Γ :{♭} Set a}(a :{♭} Γ → U) → code (decode a) ≡ a

----------------------------------------------------------------------
-- The universe is closed under Σ-types
----------------------------------------------------------------------
FibΣUniversal :
  isFib {Γ = Σ A ∈ U , (El A → U)} (λ{ (A , B) → Σ x ∈ El A , El (B x) })
FibΣUniversal e p = FibΣid α β e id where
  A : Int → Set
  A i = El (fst (p i))
  α : isFib A
  α = reindex El el (fst ∘ p)
  B : (Σ i ∈ Int , A i) → Set
  B (i , a) = El (snd (p i) a)
  β : isFib B
  β = reindex El el (λ{ (i , a) → snd (p i) a})

σ : (a : U)(b : El a → U) → U
σ a b = code ((λ{ (A , B) → Σ x ∈ El A , El (B x) }) , FibΣUniversal) (a , b)

σ' :
  {Γ : Set}
  (a : Γ → U)
  (b : Σ Γ (El ∘ a) → U)
  → ---------------
  Γ → U
σ' a b x = σ (a x) (λ a → b (x , a))

σ-comp :
  {Γ : Set}
  (a : Γ → U)
  (b : Σ Γ (El ∘ a) → U)
  → ---------------
  decode (σ' a b) ≡ FibΣ' (decode a) (decode b)
σ-comp a b =
  cong
    (λ F → reindex' F (λ x → (a x , λ a → b (x , a))))
    (code-el ((λ{ (A , B) → Σ x ∈ El A , El (B x) }), FibΣUniversal))

cong♭ :
  {ℓ ℓ' :{♭} Level}
  {A :{♭} Set ℓ}
  {B :{♭} Set ℓ'}
  (f : (_ :{♭} A) → B)
  {x y :{♭} A}
  (p : x ≡ y)
  → -----------
  f x ≡ f y
cong♭ _ refl = refl

coeΣ :
  {Γ :{♭} Set}
  {A :{♭} Fib Γ}
  (B :{♭} Fib (Σ Γ (fst A)))
  → ---------------
  Fib (Σ Γ (El ∘ code A))
coeΣ {Γ} {A} B = subst (λ A → Fib (Σ Γ (fst A))) (symm (code-el A)) B

σ-comp' :
  {Γ :{♭} Set}
  (A :{♭} Fib Γ)
  (B :{♭} Fib (Σ Γ (fst A)))
  → ---------------
  code (FibΣ' A B) ≡ σ' (code A) (code (coeΣ B))
σ-comp' {Γ} A B =
  proof:
      code (FibΣ' A B)
    ≡[ cong♭ codeFibΣ' AB=dcAB ]≡
      code (FibΣ' (decode (code A)) (decode (code B')))
    ≡[ cong♭ code (symm (σ-comp (code A) (code B'))) ]≡
      code (decode (σ' (code A) (code B')))
    ≡[ code-el' (σ' (code A) (code B')) ]≡
      σ' (code A) (code B')
  qed where
    codeFibΣ' : (AB :{♭} Σ A ∈ Fib Γ , Fib (Σ Γ (fst A))) → Γ → U
    codeFibΣ' (A , B) = code (FibΣ' A B)
    B' : Fib (Σ Γ (El ∘ code A))
    B' = coeΣ B
    AB=dcAB : (A , B) ≡ (decode (code A) , decode (code B'))
    AB=dcAB = Σext (symm (code-el A)) (symm (code-el B'))

----------------------------------------------------------------------
-- The universe is closed under Π-types
----------------------------------------------------------------------
FibΠUniversal :
  isFib {Γ = Σ A ∈ U , (El A → U)} (λ{ (A , B) → (x : El A) → El (B x) })
FibΠUniversal e p = FibΠid α β e id where
  A : Int → Set
  A i = El (fst (p i))
  α : isFib A
  α = reindex El el (fst ∘ p)
  B : (Σ i ∈ Int , A i) → Set
  B (i , a) = El (snd (p i) a)
  β : isFib B
  β = reindex El el (λ{ (i , a) → snd (p i) a})

π : (a : U)(b : El a → U) → U
π a b = code ((λ{ (A , B) → (x : El A) → El (B x) }) , FibΠUniversal) (a , b)

π' :
  {Γ : Set}
  (a : Γ → U)
  (b : Σ Γ (El ∘ a) → U)
  → ---------------
  Γ → U
π' a b x = π (a x) (λ a → b (x , a))

π-comp :
  {Γ : Set}
  (a : Γ → U)
  (b : Σ Γ (El ∘ a) → U)
  → ---------------
  decode (π' a b) ≡ FibΠ' (decode a) (decode b)
π-comp a b =
  cong
    (λ F → reindex' F (λ x → (a x , λ a → b (x , a))))
    (code-el ((λ{ (A , B) → (x : El A) → El (B x) }) , FibΠUniversal))

----------------------------------------------------------------------
-- The universe is closed under Path types
----------------------------------------------------------------------
FibPathUniversal :
  isFib {Γ = Σ A ∈ U , (El A × El A)} (λ{ (A , x , y) → x ~ y })
FibPathUniversal e p = FibPathId α e p' where
  A : Int → Set
  A i = El (fst (p i))
  α : isFib A
  α = reindex El el (fst ∘ p)
  p' : Int → Σ i ∈ Int , (A i × A i)
  p' i = i , snd (p i)

path : (a : U) → El a → El a → U
path a x y = code ((λ{ (A , x , y) → x ~ y }) , FibPathUniversal) (a , x , y)

path' :
  {Γ : Set}
  (a : Γ → U)
  → ---------------
  Σ x ∈ Γ , El (a x) × El (a x) → U
path' a (x , y , y') = path (a x) y y'
  
path-comp :
  {Γ : Set}
  (a : Γ → U)
  → ---------------
  decode (path' a) ≡ FibPath' (decode a)
path-comp a =
  cong
    (λ F → reindex' F (λ{ (x , y , y') → a x , y , y' }))
    (code-el ((λ{ (A , x , y) → x ~ y }) , FibPathUniversal))


----------------------------------------------------------------------
-- The universe is closed under Glueing
----------------------------------------------------------------------
-- This section is a lot trickier because so much of the definition
-- of glueing is abstract that Agda can't see that it's defined
-- pointwise. The module glueing2 is a copy of glueing but where
-- the fact that SGlue is pointwise is public. FibSGlueid is currently
-- postulated, but it should be straightforward (but tedious) to
-- adapt the proofs in glueing to get what we want.

open import glueing2

record GlueingData : Set₁ where
  constructor gdata
  field
    ϕ : Cof
    A : [ ϕ ] → U
    B : U
    f : (u : [ ϕ ]) → El (A u) → El B
    equiv : (u : [ ϕ ]) → Equiv' (f u)

SGlueUniversal : GlueingData → Set
SGlueUniversal (gdata ϕ A B f equiv) =
  SGlue ϕ (El ∘ A) (El B) f

FibSGlueUniversal : isFib {Γ = GlueingData} SGlueUniversal
FibSGlueUniversal e p = FibSGlueid {Φ = ϕ} (λ i → GlueingData.f (p i)) (λ i → GlueingData.equiv (p i)) α β e id where  --FibPathId α e p' where
      ϕ : Int → Cof
      ϕ = GlueingData.ϕ ∘ p
      A : (Σ i ∈ Int , [ ϕ i ]) → Set
      A (i , u) = El (GlueingData.A (p i) u)
      α : isFib A
      α = reindex El el (λ{ (i , u) → GlueingData.A (p i) u})
      B : Int → Set
      B i = El (GlueingData.B (p i))
      β : isFib B
      β = reindex El el (GlueingData.B ∘ p)

sglue-code : GlueingData → U
abstract
 sglue-code = code (SGlueUniversal , FibSGlueUniversal)

sglue-code' :
  {Γ : Set}
  (g : Γ → GlueingData)
  → ---------------
  Γ → U
sglue-code' g x = sglue-code (g x)
  
sglue-comp' :
  {Γ : Set}
  (g : Γ → GlueingData)
  → ---------------
  decode (sglue-code' g) ≡
    SGlueFib (GlueingData.ϕ ∘ g)
      (decode (λ{ (x , u) → GlueingData.A (g x) u}))
      (decode (GlueingData.B ∘ g))
      (λ x → GlueingData.f (g x))
      (λ x → GlueingData.equiv (g x))
abstract
 sglue-comp' g =
  cong
    (λ F → reindex' F g)
    (code-el (SGlueUniversal , FibSGlueUniversal))

----------------------------------------------------------------------
-- Univalence
----------------------------------------------------------------------
-- Common definitions for this section. A bit ugly that they're top
-- level, but they need to be shared across proofs.
pre : {i : Int} → [ (i ≈O) ∨ (i ≈I) ] → 𝔹
pre = OI-elim (λ{ (inl _) → false ; (inr _) → true})
makeC : (A B : U){i : Int} → [ (i ≈O) ∨ (i ≈I) ] → U
makeC A B u with pre u
... | false = A
... | true = B
makeF' : (A B : U)(f : El A → El B){i : Int}(u : [ (i ≈O) ∨ (i ≈I) ]) → El (makeC A B u) → El B
makeF' A B f u = OI-elim-dep {B = λ u → El (makeC A B u) → El B} (λ{ (inl _) → f ; (inr _) → id}) u
makeE' : (A B : U)(f : El A → El B)(e : Equiv' f){i : Int}(u : [ (i ≈O) ∨ (i ≈I) ]) → Equiv' (makeF' A B f u)
makeE' A B f e u = OI-elim-dep {B = λ u → Equiv' (makeF' A B f u)} (λ{ (inl _) → e ; (inr _) → idEquiv}) u

-- UA as a map on the universe
ua :
  {A B : U}
  (f : El A → El B)
  (e : Equiv' f)
  → ---------------
  Int → U
ua {A} {B} f e = sglue-code' (λ i → gdata (i ≈O ∨ i ≈I) (makeC A B) B (makeF' A B f) (makeE' A B f e))

-- I can't seem to prove that ua f e O ≡ A and ua f e I ≡ B "smoothly",
-- but I can show this when ua is applied to crisp families:
ua-comp :
  {Γ :{♭} Set}
  {A B :{♭} Γ → U}
  (f :{♭} (x : Γ) → El (A x) → El (B x))
  (e :{♭} (x : Γ) → Equiv' (f x))
  (i :{♭} Int)
  (x : Γ)
  → ----------------
  ua (f x) (e x) i ≡ code (SGlueFib (λ _ → i ≈O ∨ i ≈I) (decode (λ{ (x , u) → makeC (A x) (B x) u})) (decode B) (λ x → makeF' (A x) (B x) (f x)) (λ x → makeE' (A x) (B x) (f x) (e x))) x
abstract
  ua-comp {Γ} {A} {B} f e i = λ x → 
    (proof:
        ua (f x) (e x) i
      ≡[ hiddenRefl x ]≡
        sglue-code' g x
      ≡[ symm (cong (λ f → f x) (code-el' (sglue-code' g))) ]≡
        code (decode (sglue-code' g)) x
      ≡[ cong♭ (λ f → code f x) (sglue-comp' g) ]≡
        code (SGlueFib (λ _ → i ≈O ∨ i ≈I) (decode (λ{ (x , u) → C x u})) (decode B) f' e') x
      ≡[ finalStep x ]≡
        code (SGlueFib (λ _ → i ≈O ∨ i ≈I) (decode (λ{ (x , u) → makeC (A x) (B x) u})) (decode B) (λ x → makeF' (A x) (B x) (f x)) (λ x → makeE' (A x) (B x) (f x) (e x))) x
    qed)
      where
        -- Type signatures
        C : (x : Γ) → [ i ≈O ∨ i ≈I ] → U
        f' : (x : Γ)(u : [ i ≈O ∨ i ≈I ]) → El (C x u) → El (B x)
        e' : (x : Γ)(u : [ i ≈O ∨ i ≈I ]) → Equiv' (f' x u)
        g : Γ → GlueingData
        hiddenRefl : (x : Γ) → ua (f x) (e x) i ≡ sglue-code' g x
        finalStep : (x : Γ) →
           code (SGlueFib (λ _ → i ≈O ∨ i ≈I) (decode (λ{ (x , u) → C x u})) (decode B) f' e') x
             ≡ code (SGlueFib (λ _ → i ≈O ∨ i ≈I) (decode (λ{ (x , u) → makeC (A x) (B x) u})) (decode B) (λ x → makeF' (A x) (B x) (f x)) (λ x → makeE' (A x) (B x) (f x) (e x))) x
        -- Careful use of abstract to make things type check in a reasonable time
        abstract
          C x = makeC (A x) (B x)
          f' x = makeF' (A x) (B x) (f x)
          e' x = makeE' (A x) (B x) (f x) (e x)
        g x' = gdata (i ≈O ∨ i ≈I) (C x') (B x') (f' x') (e' x')
        abstract
         hiddenRefl _ = refl
         finalStep _ = refl

uaO :
  {Γ :{♭} Set}
  {A B :{♭} Γ → U}
  (f :{♭} (x : Γ) → El (A x) → El (B x))
  (e :{♭} (x : Γ) → Equiv' (f x))
  → ----------------
  (x : Γ) → ua (f x) (e x) O ≡ A x
uaO {Γ} {A} {B} f e x =
    proof:
        ua (f x) (e x) O
      ≡[ ua-comp f e O x ]≡
        code (SGlueFib (λ x → O ≈O ∨ O ≈I) (decode (λ{ (x , u) → C x u })) (decode B) (λ x → f' x) (λ x → e' x)) x
      ≡[ cong (λ f → f x) (cong♭ code (SGlueReindex' (λ x → O ≈O ∨ O ≈I) (decode (λ{ (x , u) → C x u })) (decode B) (λ x → f' x) (λ x → e' x) (λ _ → ∣ inl refl ∣))) ]≡
        code (decode A) x
      ≡[ cong (λ f → f x) (code-el' A) ]≡
        A x
    qed
      where
        C : (x : Γ) → [ O ≈O ∨ O ≈I ] → U
        C x = makeC (A x) (B x)
        f' : (x : Γ)(u : [ O ≈O ∨ O ≈I ]) → El (C x u) → El (B x)
        f' x = makeF' (A x) (B x) (f x)
        e' : (x : Γ)(u : [ O ≈O ∨ O ≈I ]) → Equiv' (f' x u)
        e' x = makeE' (A x) (B x) (f x) (e x)
        g : Γ → GlueingData
        g x = gdata (O ≈O ∨ O ≈I) (C x) (B x) (f' x) (e' x)

uaI :
  {Γ :{♭} Set}
  {A B :{♭} Γ → U} Δ
  (f :{♭} (x : Γ) → El (A x) → El (B x))
  (e :{♭} (x : Γ) → Equiv' (f x))
  → ----------------
  (x : Γ) → ua (f x) (e x) I ≡ B x
uaI {Γ} {A} {B} f e x =
    proof:
        ua (f x) (e x) I
      ≡[ ua-comp f e I x ]≡
        code (SGlueFib (λ x → I ≈O ∨ I ≈I) (decode (λ{ (x , u) → C x u })) (decode B) (λ x → f' x) (λ x → e' x)) x
      ≡[ cong (λ f → f x) (cong♭ code (SGlueReindex' (λ x → I ≈O ∨ I ≈I) (decode (λ{ (x , u) → C x u })) (decode B) (λ x → f' x) (λ x → e' x) (λ _ → ∣ inr refl ∣))) ]≡
        code (decode B) x
      ≡[ cong (λ f → f x) (code-el' B) ]≡
        B x
    qed
      where
        C : (x : Γ) → [ I ≈O ∨ I ≈I ] → U
        C x = makeC (A x) (B x)
        f' : (x : Γ)(u : [ I ≈O ∨ I ≈I ]) → El (C x u) → El (B x)
        f' x = makeF' (A x) (B x) (f x)
        e' : (x : Γ)(u : [ I ≈O ∨ I ≈I ]) → Equiv' (f' x u)
        e' x = makeE' (A x) (B x) (f x) (e x)
        g : Γ → GlueingData
        g x = gdata (I ≈O ∨ I ≈I) (C x) (B x) (f' x) (e' x)


-- We now show that ua has the correct type when applied to  ∙ ⊢ A ↦
-- families.

-- Can't use Data.paths due to size issues. Should be
-- possible to refactor to make it universe polymorphic
-- but for now I just redefine the path type specifically
-- for the universe.
PathU : U → U → Set₁
PathU A B = Σ P ∈ (Int → U) , (P O ≡ A) × (P I ≡ B)

-- UA for families
ua' :
  {Γ :{♭} Set}
  {A B :{♭} Γ → U}
  (f :{♭} (x : Γ) → El (A x) → El (B x))
  (e :{♭} (x : Γ) → Equiv' (f x))
  → ------------------
  (x : Γ) → PathU (A x) (B x)
ua' {A} {B} f e x = (ua (f x) (e x)) , uaO f e x , uaI f e x
