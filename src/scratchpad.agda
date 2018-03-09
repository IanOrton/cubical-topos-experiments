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

{-# OPTIONS --rewriting --allow-unsolved-metas #-}
module scratchpad where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.products
open import Data.paths
open import Data.id
open import equivs hiding (qinv2equiv)

----------------------------------------------------------------------
-- This module contains work in progress
----------------------------------------------------------------------

----------------------------------------------------------------------
-- The function qinv2equiv that maps quasi inverses to equivalences        
----------------------------------------------------------------------

-- First, define a helper c.f. Lemma 4.2.5. in the HoTT book:

helper : {A B : Set}{β : Fib {Γ = Unit} (λ _ → B)}(f : A → B)(x x' : A)(y : B)(p : f x ~ y)(p' : f x' ~ y)
  → (Σ q ∈ (x ~ x') , (transPath β (congPath f q) p') ~ p)
  → (x , p) ~ (x' , p')
helper {A} {B} {β} f x x' y p p' (q , r) = ((λ i → fst q i , fst (pth i)) , atO , atI) where
  q' : (i : Int) → fst q i ~ x'
  fst (q' i) j = fst q (max i j)
  snd (q' i) = (refl , snd (snd q))

  sndCase : f (fst q I) ~ y
  sndCase = (fst p' , trans (cong f (symm (snd (snd q)))) (fst (snd p')) , snd (snd p'))

  -- transPth : transPath β (congPath f (q' I)) p' ~ (fst p' , trans (cong f (symm (snd (snd q)))) (fst (snd p')) , snd (snd p'))
  -- transPth = {!!} where 
      
  transPth : fst (transPath β (congPath f (q' I)) p') ~ fst p'
  transPth = {!!} where -- ((λ i j → fst (b' i j)) , (funext (λ j → symm (snd (b' O j) ∣ inl refl ∣))) , funext (λ j → symm (snd (b' I j) ∣ inr refl ∣))) where
      ends : (i j : Int) → [ (i ≈O ∨ i ≈I) ∨ (j ≈O ∨ j ≈I) ] → Π (λ _ → B)
      ends i j u = OI-elim' (icases i j) (jcases i j) ijAgree u where
        icases : (i j : Int) → (i ≡ O) ⊎ (i ≡ I) → Π (λ _ → B)
        icases .O j (inl refl) k = fst (transPath β (congPath f (q' I)) p') j
        icases .I j (inr refl) k = fst p' j
        jcases : (i j : Int) → (j ≡ O) ⊎ (j ≡ I) → Π (λ _ → B)
        jcases i .O (inl refl) k = f x'
        jcases i .I (inr refl) k = y
        ijAgree : {i j : Int}(e e' : OI) (p₁ : i ≡ ⟨ e ⟩) (q₁ : j ≡ ⟨ e' ⟩) → icases i j (OIinj i e p₁) ≡ jcases i j (OIinj j e' q₁)
        ijAgree O' O' refl refl = funext (λ _ → let rr = fst (snd (transPath β (congPath f (q' I)) p')) in trans (cong f (snd (snd q))) rr)
        ijAgree O' I' refl refl = funext (λ _ → snd (snd (transPath β (congPath f (q' I)) p')))
        ijAgree I' O' refl refl = funext (λ _ → fst (snd p'))
        ijAgree I' I' refl refl = funext (λ _ → snd (snd p'))
      agrees : (i j : Int) → prf ((((i ≈O ∨ i ≈I) ∨ j ≈O ∨ j ≈I) , ends i j) ∙ I ↗ y)
      agrees i j u = or-elim-eq (λ v → ends i j v I) y (λ {l} → left i j l) (λ {r} → right i j r) u where
        left : (i j : Int)(l : prf (i ≈ O or i ≈ I)) → ends i j ∣ inl l ∣ I ≡ y
        left i j v = or-elim-eq (λ v → ends i j ∣ inl v ∣ I) y (λ {l} → ll i j l) {!!} v where
          ll : (i j : Int)(l : i ≡ O) → ends i j ∣ inl ∣ inl l ∣ ∣ I ≡ y
          ll .O j refl = {!!} --snd (snd (transPath β (congPath f (q' I)) p'))
        right : (i j : Int)(r : prf (j ≈ O or j ≈ I)) → ends i j ∣ inr r ∣ I ≡ y
        right _ _ =  {!!} -- snd (snd p')
      b' : (i j : Int) → ⟦ b ∈ B ∣ (((i ≈O ∨ i ≈I) ∨ (j ≈O ∨ j ≈I)) , ends i j) ∙ O ↗ b ⟧
      b' i j = β I' (λ _ → tt) ((i ≈O ∨ i ≈I) ∨ (j ≈O ∨ j ≈I)) (ends i j) (fst p' j , {!!})

  -- transPth : fst (transPath β (congPath f (q' I)) p') ~ fst p'
  -- transPth = {!!} where -- ((λ i j → fst (b' i j)) , (funext (λ j → symm (snd (b' O j) ∣ inl refl ∣))) , funext (λ j → symm (snd (b' I j) ∣ inr refl ∣))) where
  --     ends : (i : Int) → [ i ≈O ∨ i ≈I ] → Π (λ _ → B)
  --     ends i u = {!!}
  --     -- OI-elim' (icases i j) (jcases i j) ijAgree u where
  --     --   icases : (i j : Int) → (i ≡ O) ⊎ (i ≡ I) → Π (λ _ → B)
  --     --   icases .O j (inl refl) k = fst (transPath β (congPath f (q' I)) p') j
  --     --   icases .I j (inr refl) k = fst p' j
  --     --   jcases : (i j : Int) → (j ≡ O) ⊎ (j ≡ I) → Π (λ _ → B)
  --     --   jcases i .O (inl refl) k = f x'
  --     --   jcases i .I (inr refl) k = y
  --     --   ijAgree : {i j : Int}(e e' : OI) (p₁ : i ≡ ⟨ e ⟩) (q₁ : j ≡ ⟨ e' ⟩) → icases i j (OIinj i e p₁) ≡ jcases i j (OIinj j e' q₁)
  --     --   ijAgree O' O' refl refl = funext (λ _ → let rr = fst (snd (transPath β (congPath f (q' I)) p')) in trans (cong f (snd (snd q))) rr)
  --     --   ijAgree O' I' refl refl = funext (λ _ → snd (snd (transPath β (congPath f (q' I)) p')))
  --     --   ijAgree I' O' refl refl = funext (λ _ → fst (snd p'))
  --     --   ijAgree I' I' refl refl = funext (λ _ → snd (snd p'))
  --     agrees : (i : Int) → prf (((i ≈O ∨ i ≈I) , ends i) ∙ I ↗ y)
  --     agrees i u = {!!}
  --     -- or-elim-eq (λ v → ends i v I) y (λ {l} → left i j l) (λ {r} → right i j r) u where
  --     --   left : (i j : Int)(l : prf (i ≈ O or i ≈ I)) → ends i j ∣ inl l ∣ I ≡ y
  --     --   left i j v = or-elim-eq (λ v → ends i j ∣ inl v ∣ I) y (λ {l} → ll i j l) {!!} v where
  --     --     ll : (i j : Int)(l : i ≡ O) → ends i j ∣ inl ∣ inl l ∣ ∣ I ≡ y
  --     --     ll .O j refl = {!!} --snd (snd (transPath β (congPath f (q' I)) p'))
  --     --   right : (i j : Int)(r : prf (j ≈ O or j ≈ I)) → ends i j ∣ inr r ∣ I ≡ y
  --     --   right _ _ =  {!!} -- snd (snd p')
  --     b' : (i : Int) → {!!} -- ⟦ b ∈ B ∣ (((i ≈O ∨ i ≈I) ∨ (j ≈O ∨ j ≈I)) , ends i j) ∙ I ↗ b ⟧
  --     b' i = fill O' β (λ _ → tt) (i ≈O ∨ i ≈I) (ends i) y {!!}

  ff : (i : Int) → [ i ≈O ∨ i ≈I ] → Π (λ j → Path (λ _ → B) (tt , f (fst q i) , y))
  ff i u = OI-elim cases u where
    cases : {i : Int} → (i ≡ O) ⊎ (i ≡ I) → Int → (f (fst q i) ~ y)
    cases (inl refl) j = (fst (fst r j) , (trans (cong f (symm (fst (snd q)))) (fst (snd (fst r j)))) , snd (snd (fst r j)))
    cases (inr refl) j = (fst transPth j , {!!} , (let rr = snd (snd (transPth)) in {!!}))
  pth : (i : Int) → ⟦ pth ∈ (f (fst q i) ~ y) ∣ ((i ≈O ∨ i ≈I) , ff i) ∙ I ↗ pth ⟧
  pth i = FibPath β O' (λ j → (tt , f (fst q i) , y)) (i ≈O ∨ i ≈I) (ff i) ((transPath β (congPath f (q' i)) p' , extends)) where
    extends : prf (((i ≈O ∨ i ≈I) , ff i) ∙ O ↗ transPath β (congPath f (q' i)) p')
    extends u = or-elim-eq (λ v → ff i v O) (transPath β (congPath f (q' i)) p') (λ {l} → left i l) (λ {r} → right i r) u where
      left : (i : Int)(l : i ≡ O) → ff i ∣ inl l ∣ O ≡ transPath β (congPath f (q' i)) p'
      left .O refl = PathExt (let tt = cong fst (fst (snd r)) in trans (abc (symm (fst (snd q))) refl) tt) where
        abc : {x₀ x₁ : A}(xeq : x₀ ≡ x₁){q : x₀ ~ x'}{q' : x₁ ~ x'}
          → (fst q ≡ fst q')
          → fst (transPath β (congPath f q) p') ≡ fst (transPath β (congPath f q') p')
        abc refl refl = cong (λ q → fst (transPath β (congPath f q) p')) (PathExt refl)
      right : (i : Int)(r : i ≡ I) → ff i ∣ inr r ∣ O ≡ transPath β (congPath f (q' i)) p'
      right .I refl = PathExt ({!!} fst (snd transPth))
  
  atO : (fst q O , fst (pth O)) ≡ (x , p)
  atO = fiberext (fst (snd q)) (let tt = snd (pth O) ∣ inl refl ∣ in let ss = cong fst (symm tt) in trans (cong fst (snd (snd r))) ss)
  
  atI : (fst q I , fst (pth I)) ≡ (x' , p')
  atI = {!!} -- fiberext (snd (snd q)) (trans (snd (snd transPth)) (? cong fst (symm (snd (pth I) ∣ inr refl ∣)))) --(cong fst (symm (snd (pth I) ∣ inr refl ∣)))


qinv2equiv :
  {Γ : Set}{A B : Γ → Set}(α : Fib A)(β : Fib B)
  (f : (x : Γ) → A x → B x)(x : Γ) → Qinv (f x) → Equiv (f x)
fst (fst (qinv2equiv _ _ _ _ (g , _ , _) b)) = g b
snd (fst (qinv2equiv _ _ _ _ (_ , fg=id , _) b)) = fg=id b
snd (qinv2equiv {Γ} {A} {B} α β f x (g , fg=id , gf=id) b) (a , p) = helper (f x) (g b) a b (fg=id b) p {!!} where

--helper (f x) (fst qinv b) a b (fst (snd qinv) b) p {!!} --(path , pathO , pathI) where
  -- rr : fst qinv (f x a) ~ a
  -- rr = snd (snd (qinv)) a
  -- ss : fst qinv (f x a) ~ fst qinv b
  -- ss = congPath (fst qinv) p
  -- tt : a ~ fst qinv b
  -- tt = transPath ? ? ? --(symss
  -- ww : (i : Int) → fst tt i ~ a
  -- fst (ww i) j = fst tt (max i j)
  -- snd (ww i) = (refl , snd (snd tt))
  -- qq : (i : Int) → f x (fst tt i) ~ b
  -- qq i = transPath β (congPath (f x) (ww i)) p
  -- path : Int → Σ a ∈ A x , f x a ~ b
  -- path i = (fst tt i , qq i)
  -- pathO : path O ≡ (fst qinv b , fst (snd qinv) b)
  -- pathO = Σext (fst (snd tt)) {!!} 
  -- pathI : path I ≡ (a , p)
  -- pathI = Σext (snd (snd tt)) {!!} 

-- fst (fst (qinv2equiv _ _ _ _ (g , _ , _) b)) = g b
-- snd (fst (qinv2equiv _ _ _ _ (_ , fg=id , _) b)) = fg=id b
-- snd (qinv2equiv {Γ} {A} {B} α β f x (g , fg~id , gf~id) b) (a , p) =
--   ((λ i → (fst (congPath g p) i , toB i)) , {!!} , {!!}) where
--     step₁ : (i : Int) → f x (g (fst p i)) ~ fst p i
--     step₁ i = fg~id (fst p i)
--     step₂ : (i : Int) → fst p i ~ fst p I
--     fst (step₂ i) j = fst p (max i j)
--     snd (step₂ i) = (refl , refl)
--     concat : (i : Int) → f x (g (fst p i)) ~ fst p I
--     concat i = transPath (λ e p₁ → β e (λ _ → x)) (step₁ i) (step₂ i)
--     toB : (i : Int) → f x (g (fst p i)) ~ b
--     toB i = subst (λ b → f x (g (fst p i)) ~ b) (snd (snd p)) (concat i)

-- helper {!!} (fg~id b) p where
--   helper :{a a' : A x}(p : a ~ a')(q : f x a ~ b)(r : f x a' ~ b) → (a , q) ~ (a' , r)
--   helper {a} {a'} p q r = ((λ i → (fst p i , pathi i)) , {!!} , {!!}) where
--     qr : (i : Int) → [ i ≈O ∨ i ≈I ] → Π (λ _ → B x)
--     qr i u = OI-elim (λ{ (inl _) → fst q ; (inr _) → fst r }) u
--     extends : (i : Int) → prf (((i ≈O ∨ i ≈I) , qr i) ∙ I ↗ b)
--     extends i u = or-elim-eq (λ u → qr i u I) b (snd (snd q)) (snd (snd r)) u
--     path : (i : Int) → ⟦ p ∈ (Π (λ _ → B x)) ∣ (((i ≈O ∨ i ≈I) , qr i) ↗ p) & (p I ≈ b) ⟧
--     path i = fill I' β (λ _ → x) (i ≈O ∨ i ≈I) (qr i) b (extends i)
--     pathO~b : (i : Int) → fst (path i) O ~ b
--     fst (pathO~b i) = fst (path i)
--     snd (pathO~b i) = (refl , snd (snd (path i)))
--     ai : (i : Int) → A x
--     ai i = g (fst (path i) O)
--     pathi : (i : Int) → f x (fst p i) ~ b
--     pathi i = let rr = fg~id (fst (path i) O) in {!!} --transPath (λ e p₁ → β e (λ _ → x)) rr (pathO~b i)

--     aiO : ai O ≡ a
--     aiO = {!!}

-- A' : Unit → Set
    -- A' _ = A x
    -- α' : Fib A'
    -- α' e p = α e (λ _ → x)
    -- PathB : Σ Unit A' → Set
    -- PathB (_ , a) = f x a ~ b
    -- fibPathB : Fib PathB
    -- fibPathB e p = FibPath β e (λ i → (x , f x (snd (p i)) , b))
    -- γ : Fib (Σ' A' PathB)
    -- γ = FibΣ {B = PathB} α' fibPathB

  -- helper :{a a' : A x}(p : a ~ a')(q : f x a ~ b)(r : f x a' ~ b) → (a , q) ~ (a' , r)
  -- fst (helper p q r) i = (fst p i , pathi) where
  --   pathi : f x (fst p i) ~ b
  --   pathi = (fst path , {!!} , snd (snd path)) where
  --     qr : [ i ≈O ∨ i ≈I ] → Π (λ _ → B x)
  --     qr u = OI-elim (λ{ (inl _) → fst q ; (inr _) → fst r }) u
  --     extends : prf (((i ≈O ∨ i ≈I) , qr) ∙ I ↗ b)
  --     extends u = or-elim-eq (λ u → qr u I) b (snd (snd q)) (snd (snd r)) u
  --     path : ⟦ p ∈ (Π (λ _ → B x)) ∣ (((i ≈O ∨ i ≈I) , qr ) ↗ p) & (p I ≈ b) ⟧
  --     path = fill I' β (λ _ → x) (i ≈O ∨ i ≈I) qr b extends
  -- snd (helper p q r) = {!!}


-- (path , pathO , pathI) where
--   rr : fst qinv (f x a) ~ a
--   rr = snd (snd (qinv)) a
--   ss : fst qinv (f x a) ~ fst qinv b
--   ss = congPath (fst qinv) p
--   tt : fst qinv b ~ a
--   tt = transPath α x ss rr
--   ww : (i : Int) → fst tt i ~ a
--   fst (ww i) j = fst tt (max i j)
--   snd (ww i) = (refl , snd (snd tt))
--   qq : (i : Int) → f x (fst tt i) ~ b
--   qq i = transPath β x (congPath (f x) (symmPath α x (ww i))) p
--   path : Int → Σ a ∈ A x , f x a ~ b
--   path i = (fst tt i , qq i)
--   pathO : path O ≡ (fst qinv b , fst (snd qinv) b)
--   pathO = Σext (fst (snd tt)) {!!} 
--   pathI : path I ≡ (a , p)
--   pathI = Σext (snd (snd tt)) {!!} 


