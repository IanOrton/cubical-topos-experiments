{-# OPTIONS --rewriting #-}

module quotient where
 
open import prelude public
open import Agda.Builtin.TrustMe

----------------------------------------------------------------------
-- Quotient sets
----------------------------------------------------------------------
infix 6 [_]/_
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
--qeq _ _ = {!!}

-- generating equalities
-- qeqRefl :
--   {ℓ ℓ' : Level}
--   {A : Set ℓ}
--   {x : A}
--   (R : A → A → Set ℓ')
--   (r : R x x)
--   → ------------------
--   qeq R r ≡ refl
-- qeqRefl R r = {!!}

postulate
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
--qind-comp _ _ _ _ _ = primTrustMe

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE qind-comp   #-}

--quotient elimination
qelim :
  {ℓ ℓ' ℓ'' : Level}
  {A : Set ℓ}
  (R : A → A → Set ℓ')
  (B : Set ℓ'')
  (f : A → B)
  (e : (x y : A)(r : R x y) → f x ≡ f y)
  → ------------------------------------
  A / R → B
qelim R B f e =
  qind R (λ _ → B) f
  (λ x y r → trans (e x y r) (substconst B (qeq R r) (f x)))

qelim-comp :
  {ℓ ℓ' ℓ'' : Level}
  {A : Set ℓ}
  (R : A → A → Set ℓ')
  (B : Set ℓ'')
  (f : A → B)
  (e : (x y : A)(r : R x y) → f x ≡ f y)
  (x : A)
  → ------------------------------------
  qelim R B f e ([ x ]/ R) ≡ f x
qelim-comp _ _ _ _ _ = refl

qelim-uniq :
  {ℓ ℓ' ℓ'' : Level}
  {A : Set ℓ}
  (R : A → A → Set ℓ')
  (B : Set ℓ'')
  (f : A → B)
  (e : (x y : A)(r : R x y) → f x ≡ f y)
  (g : A / R → B)
  (_ : (x : A) → f x ≡ g ([ x ]/ R))
  → ------------------------------------
  (y : A / R) → qelim R B f e y ≡ g y
qelim-uniq R B f e g h =
  qind R (λ y → qelim R B f e y ≡ g y)
  (λ x → trans (h x) (qelim-comp R B f e x))
  (λ _ _ _  → uipImp)

----------------------------------------------------------------------
-- Function extensionalty via quotients
----------------------------------------------------------------------
funext :
  {ℓ  ℓ' : Level}
  {A : Set ℓ}
  {B : A → Set ℓ'}
  {f g : (x : A) → B x}
  (_ : (x : A) → f x ≡ g x)
  → -----------------------
  f ≡ g
funext {A = A} {B} {f} {g} h = cong m (qeq R r) where
  data s≡t : Set where
    s : s≡t
    t : s≡t
  data R : s≡t → s≡t → Set where
    r : R s t
  k : (x : A) → s≡t → B x
  k x s = f x
  k x t = g x

  l : (x : A)(b b' : s≡t) → R b b' → k x b ≡ k x b'
  l x _ _ r = h x
   
  m : s≡t / R → (x : A) → B x
  m z x = qelim R (B x) (k x) (l x) z 


----------------------------------------------------------------------
-- Tests
----------------------------------------------------------------------
qelim₂ : 
  {ℓ ℓ' ℓ'' : Level}
  {A : Set ℓ}
  (R : A → A → Set ℓ')
  (B : Set ℓ'')
  (f : A → A → B)
  (e : (x x' : A)(rx : R x x')(y : A) → f x y ≡ f x' y)
  (e' : (x : A)(y y' : A)(ry : R y y') → f x y ≡ f x y')
  → ------------------------------------
  A / R → A / R → B
qelim₂ {A = A} R B f e e' = f'' where
  f' : A → A / R → B
  f' a = qelim R B (f a) (e' a)
  f'' : A / R → A / R → B
  f'' = qelim R (A / R → B) f' resp where
    resp : (x y : A) → R x y → f' x ≡ f' y
    resp x y r = funext (qind R (λ q → f' x q ≡ f' y q) (e x y r) (λ _ _ _ → uipImp))
  

----------------------------------------------------------------------
-- Tests
----------------------------------------------------------------------
record Equiv{ℓ ℓ' : Level}(A : Set ℓ)(B : Set ℓ') : Set (ℓ ⊔ ℓ') where
 constructor equiv
 field
  f : A → B
  g : B → A
  fg≡id : (x : B) → f (g x) ≡ x
  gf≡id : (x : A) → g (f x) ≡ x

data ⊥ {ℓ : Level}{A : Set ℓ} : A → A → Set ℓ where

-- quoBy⊥ : 
--   {ℓ : Level}
--   {A : Set ℓ}
--   → -----------------------
--   Equiv A (A / ⊥)
-- quoBy⊥ {A = A} = equiv f g fg≡id (λ _ → refl) where
--   f : A → A / ⊥
--   f a = [ a ]/ ⊥

--   g : A / ⊥ → A
--   g x = qelim ⊥ A (λ z → z) (λ _ _ → λ ()) x

--   fg≡id : (x : A / ⊥) → f (g x) ≡ x
--   fg≡id x = qind ⊥ (λ x → f (g x) ≡ x) (λ _ → refl) (λ x₁ y → λ ()) x

open import Data.Nat
open import Data.Fin
open import Data.Unit

narg : Set → ℕ → Set
narg A zero = ⊤
narg A (suc n) = A × narg A n

nmap : {A B : Set}{n : ℕ} → (A → B) → narg A n → narg B n
nmap {n = zero} _ unit = unit
nmap {n = suc n} f (x , xs) = (f x) , (nmap f xs)

nary : {l : Level} → Set → Set l → ℕ → Set l
nary A B zero = B
nary A B (suc n) = A → nary A B n

napp : {l : Level} → {A : Set}{B : Set l}(n : ℕ) → nary A B n → narg A n → B
napp zero b tt = b
napp (suc n) f (x , xs) = napp n (f x) xs

nary-dep : (A : Set)(n : ℕ) → (nary A Set n) → Set
nary-dep A zero B = B
nary-dep A (suc n) B = (x : A) → nary-dep A n (B x)

nary-≡ : {A : Set}{B : Set}(n : ℕ)(f g : nary A B n) → Set
nary-≡ zero f g = f ≡ g
nary-≡ {A} (suc n) f g = (x : A) → nary-≡ n (f x) (g x)

nary-uip : {A : Set}{B : Set}(n : ℕ){f g : nary A B n}{p q : nary-≡ n f g} → p ≡ q
nary-uip zero = uipImp
nary-uip (suc n) = funext (λ x → nary-uip n)

nary-funext : {A : Set}{B : Set}(n : ℕ)(f g : nary A B n) → nary-≡ n f g → f ≡ g
nary-funext zero f g ptwise = ptwise
nary-funext (suc n) f g ptwise = funext (λ x → nary-funext n (f x) (g x) (ptwise x))

data T : Set where
 t : T

record Rel {A : Set}(R : A → A → Set) : Set where
  constructor _~_by_
  field
    lft : A
    rgt : A
    rel : R lft rgt

open Rel

nary-resp : (A : Set)(R : A → A → Set)(B : Set)(n : ℕ)(f : nary A B n)(k : Fin n) → Set
nary-resp A R B (suc n) f zero = (x~r~x' : Rel R) → nary-≡ n (f (lft x~r~x')) (f (rgt x~r~x'))
nary-resp A R B (suc n) f (suc k) = (x : A) → nary-resp A R B n (f x) k

nary-resp-unique : {A : Set}{R : A → A → Set}{B : Set}(n : ℕ)(f : nary A B n)(k : Fin n){resp resp' : nary-resp A R B n f k} → resp ≡ resp'
nary-resp-unique (suc n) f zero {resp} {resp'} = funext (λ _ → nary-uip n)
nary-resp-unique (suc n) f (suc k) {resp} {resp'} = funext (λ x → nary-resp-unique n (f x) k {resp x} {resp' x})

module Tests where
  postulate
    f : nary ℕ T 5

  data R : ℕ → ℕ → Set where
    rt : (m n : ℕ) → R m n

  test'   = nary-resp ℕ R T 5 f zero
  test''  = nary-resp ℕ R T 5 f (suc (suc zero))
  test''' = nary-resp ℕ R T 5 f (suc (suc (suc (suc zero))))

cong₂dep :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  {A' : A → Set ℓ}
  {B : Set ℓ'}
  (f : (x : A) → A' x → B)
  {x x'  : A}
  {y : A' x}
  {y' : A' x'}
  (p : x ≡ x')
  (q : subst A' p y ≡ y')
  → --------------
  f x y ≡ f x' y'
cong₂dep _ refl refl = refl

qelim-n : 
  {A : Set}
  (R : A → A → Set)
  (B : Set)
  (n : ℕ)
  (f : nary A B n)
  (resp : (k : Fin n) → nary-resp A R B n f k)
  → ------------------------------------
  nary (A / R) B n
qelim-n R B zero b resp = b
qelim-n {A} R B (suc n) f resp = qelim R (nary (A / R) B n) f' resp' where
  f' : A → nary (A / R) B n
  f' x = qelim-n R B n (f x) (λ k → resp (suc k) x)
  resp' : (x y : A) → R x y → f' x ≡ f' y
  resp' x y r = cong₂dep (qelim-n R B n) fx=fy (funext (λ k → nary-resp-unique n (f y) k)) where
    fx=fy : f x ≡ f y
    fx=fy = nary-funext n (f x) (f y) (resp zero (x ~ y by r))

qelim-comp-n :
  {A : Set}
  (R : A → A → Set)
  (B : Set)
  (n : ℕ)
  (f : nary A B n)
  (resp : (k : Fin n) → nary-resp A R B n f k)
  (xs : narg A n)
  → ------------------------------------
  napp n (qelim-n R B n f resp) (nmap (λ x → [ x ]/ R) xs) ≡ napp n f xs
qelim-comp-n _ _ zero _ _ _ = refl
qelim-comp-n R B (suc n) f resp (x , xs) = qelim-comp-n R B n (f x) (λ k → resp (suc k) x) xs


syntax qelim R B (λ x → y) r = elimfrom R to B when x gives y andresps r
--syntax qelim R B f r = elimfrom R to B when x gives y andresps r
