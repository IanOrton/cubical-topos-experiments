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
module univalence-working2 where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.products
open import Data.functions
open import Data.paths
open import equivs
open import glueing
open import univalence-working


pathInv : {A B : Set}(P : IdU A B)(ρ : Fib (fst P))(i : Int) → IdU (fst P i) (fst (fst (pathToPath P ρ)) i)
pathInv (P , refl , refl) ρ i = subst (λ P' → (Fib P' → IdU (P i) (P' i))) eqTypes result (snd (pathToPath (P , refl , refl) ρ)) where
  a~fa : (a : P O) → Π P
  a~fa a = fst (fill {A = P} O' ρ id cofFalse ∅-elim a (λ ()))
  a~faAtO : (a : P O) → a~fa a O ≡ a
  a~faAtO a = snd (snd (fill {A = P} O' ρ id cofFalse ∅-elim a (λ ())))
  gb~b : (b : P I) → Π P
  gb~b b = fst (fill I' ρ id cofFalse ∅-elim b (λ ()))
  f : P O → P I
  f a = a~fa a I
  C : res Int Φ → Set
  C = makeC (P O) (P I) f
  f' : (i : Int)(u : [ Φ i ]) → C (i , u) → P I
  f' = makeF' (P O) (P I) f
  P' : Int → Set
  P' = SGlue Φ C (λ _ → P I) f'
  fEq : f ≡ fst (idToEquiv (P , refl , refl) ρ)
  fEq = funext (λ a → refl)
  eqTypes : P' ≡ fst (fst (pathToPath (P , refl , refl) ρ))
  eqTypes =
    proof:
      P'
        ≡[ refl ]≡
      SGlue Φ (makeC (P O) (P I) f) (λ _ → P I) (makeF' (P O) (P I) f)
        ≡[ cong (λ f → SGlue Φ (makeC (P O) (P I) f) (λ _ → P I) (makeF' (P O) (P I) f)) fEq ]≡
      SGlue Φ (makeC (P O) (P I) (fst (idToEquiv (P , refl , refl) ρ))) (λ _ → P I) (makeF' (P O) (P I) (fst (idToEquiv (P , refl , refl) ρ)))
        ≡[ refl ]≡
      fst (fst (pathToPath (P , refl , refl) ρ))
    qed
    
  q : (i : Int) → P i → [ Φ i ] → Π (P ∘ (λ j → max i j))
  q i p u = OI-elim (cases p) u where
    cases : {i : Int} → P i → (i ≡ O) ⊎ (i ≡ I) → (j : Int) → P (max i j)
    cases p (inl refl) = a~fa p
    cases p (inr refl) _ = p
    
  qAtO : (i : Int)(p : P i) → prf ((Φ i , (q i p)) ∙ O ↗ p)
  qAtO i p u = OI-elim-dep {B = λ u → snd ((Φ i , (q i p)) ∙ O) u ≡ p} (cases' p) u where
        cases' : {i : Int}(p : P i)(u : (i ≡ O) ⊎ (i ≡ I)) → q i p ∣ u ∣ O ≡ p
        cases' p (inl refl) = snd (snd (fill {A = P} O' ρ id cofFalse ∅-elim p (λ ())))
        cases' p (inr refl) = refl

  pAsC : (i : Int)(p : P i)(u : [ Φ i ]) → C (i , u)
  pAsC i p u = OI-elim-dep {B = λ u → P i → C (i , u)} (cases) u p where
    cases : {i : Int}(u : (i ≡ O) ⊎ (i ≡ I)) → P i → C (i , ∣ u ∣)
    cases (inl refl) pO = pO
    cases (inr refl) pI = pI

  g : (i : Int) → P i → P' i
  g i p = str {Φ = Φ} {A = C} {B = λ _ → P I} f' i (pAsC i p , b i p , (λ u → OI-elim-dep {B = λ u → f' i u (pAsC i p u) ≡ b i p} (fp≡b p) u))  where
        b : (i : Int)(p : P i) → P I
        b i p = fst (ρ O' (λ j → max i j) (Φ i) (q i p) (p , qAtO i p)) where
        fp≡b : {i : Int}(p : P i)(u : (i ≡ O) ⊎ (i ≡ I)) → f' i ∣ u ∣ (pAsC i p ∣ u ∣) ≡ b i p
        fp≡b p (inl refl) = snd (ρ O' (λ j → j) (Φ O) (q O p) (p , qAtO O p)) ∣ inl refl ∣  
        fp≡b p (inr refl) = snd (ρ O' (λ _ → I) (Φ I) (q I p) (p , qAtO I p)) ∣ inr refl ∣
       
  open import Agda.Builtin.TrustMe
  c : (i : Int)(p' : P' i)(u : [ Φ i ]) → C (i , u)
  c i p' = fst (unstr {Φ = Φ} {A = C} {B = λ _ → P I} f' i p')
  b : (i : Int)(p' : P' i) → P I
  b i p' = fst (snd (unstr {Φ = Φ} {A = C} {B = λ _ → P I} f' i p'))
  fc↗b : (i : Int)(p' : P' i)(u : [ Φ i ]) → f' i u (c i p' u) ≡ b i p'
  fc↗b i p' = snd (snd (unstr {Φ = Φ} {A = C} {B = λ _ → P I} f' i p'))
  q' : (i : Int)(p' : P' i) → [ Φ i ] → Π (P ∘ (λ j → max i j))
  q' i p' u = OI-elim (cases p' u) u where
    cases : {i : Int}(p' : P' i)(u : [ Φ i ]) → (i ≡ O) ⊎ (i ≡ I) → (j : Int) → P (max i j)
    cases p' u (inl refl) = q O (c O p' ∣ inl refl ∣) ∣ inl refl ∣ 
    cases p' u (inr refl) = q I (c I p' ∣ inr refl ∣) ∣ inr refl ∣ 
  q'I↗b : (i : Int)(p' : P' i) → prf ((Φ i , q' i p') ∙ I ↗ b i p')
  q'I↗b i p' u = OI-elim-dep {B = λ u → q' i p' u I ≡ b i p'} (cases p') u where
    cases : {i : Int}(p' : P' i)(u : (i ≡ O) ⊎ (i ≡ I)) → q' i p' ∣ u ∣ I ≡ b i p'
    cases p' (inl refl) = fc↗b O p' ∣ inl refl ∣
    cases p' (inr refl) = fc↗b I p' ∣ inr refl ∣
  hRaw : (i : Int)(p' : P' i) → ⟦ p ∈ (P i) ∣ (Φ i , q' i p') ∙ O ↗ p ⟧
  hRaw i p' = ρ I' (λ j → max i j) (Φ i) (q' i p') (b i p' , q'I↗b i p')
  h : (i : Int) → P' i → P i
  h i p' = fst (hRaw i p')

  hO≡cO : (p' : P' O) → h O p' ≡ c O p' ∣ inl refl ∣
  hO≡cO p' =
    proof:
      h O p'
        ≡[ symm (snd (hRaw O p') ∣ inl refl ∣) ]≡
      a~fa (c O p' ∣ inl refl ∣) O
        ≡[ a~faAtO (c O p' ∣ inl refl ∣) ]≡
      c O p' ∣ inl refl ∣
    qed
    
  gFiller : (i : Int)(p : P i) → ⟦ f ∈ ((j : Int) → P (max i j)) ∣ ((Φ i , q i p) ↗ f) & (f O ≈ p) ⟧
  gFiller i p = fill O' ρ (λ j → max i j) (Φ i) (q i p) p (qAtO i p)
  gPath : (i : Int)(p : P i) → _~~_ {A = λ j → P (max i j)} p (b i (g i p))
  gPath i p = (path , pathO≡p , pathI≡bg) where
    path : (j : Int) → P (max i j)
    path = fst (gFiller i p)
    pathO≡p : path O ≡ p
    pathO≡p = snd (snd (gFiller i p))
    pathI≡bg : path I ≡ fst (snd (unstr {Φ = Φ} {A = C} {B = λ _ → P I} f' i (g i p)))
    pathI≡bg =
      proof:
        path I
          ≡[ fillAtEnd {A = P} O' ρ (λ j → max i j) (Φ i) (q i p) p (qAtO i p) ]≡
        fst (ρ O' (λ j → max i j) (Φ i) (q i p) (p , qAtO i p))
          ≡[ cong (λ eq → fst (snd eq)) (appCong (symm (unstrStr {Φ = Φ} {A = C} {B = λ _ → P I} f' i))) ]≡
        fst (snd (unstr {Φ = Φ} {A = C} {B = λ _ → P I} f' i (g i p)))
      qed
      
  hFiller : (i : Int)(p' : P' i) → ⟦ f ∈ ((j : Int) → P (max i j)) ∣ ((Φ i , q' i p') ↗ f) & (f I ≈ b i p') ⟧
  hFiller i p' = fill {A = P} I' ρ (λ j → max i j) (Φ i) (q' i p') (b i p') (q'I↗b i p')
  hPath : (i : Int)(p' : P' i) → _~~_ {A = λ j → P (max i j)} (h i p') (b i p')
  hPath i p' = (path , pathO≡hp' , pathI≡b) where
    path : (j : Int) → P (max i j)
    path = fst (hFiller i p')
    pathO≡hp' : path O ≡ h i p'
    pathO≡hp' = primTrustMe   -- For speed, real term: fillAtEnd {A = P} I' ρ (λ j → max i j) (Φ i) (q' i p') (b i p') (q'I↗b i p')
      -- proof:
      --   fst filler O  
      --     ≡[ fillAtEnd {A = P} I' ρ (λ j → max i j) (Φ i) (q' i p') (b i p') (q'I↗b i p') ]≡ 
      --   fst (ρ I' (λ j → max i j) (Φ i) (q' i p') (b i p' , q'I↗b i p'))   
      --     ≡[ refl ]≡
      --   h i p'
      -- qed
    pathI≡b : path I ≡ b i p'
    pathI≡b = snd (snd (hFiller i p'))

  hgInv : (p : P i) → h i (g i p) ~ p
  hgInv p = transDep {α = λ e p → ρ e (λ j → max i (p j))} (hPath i (g i p)) (gPath i p)

  ghInv : (p' : P' i) → g i (h i p') ~ p'
  ghInv p' = (path , pathO≡ghp' , pathI≡p') where
    fstEq : c i p' ≡ c i (g i (h i p'))
    fstEq = funext body where
      body : (u : [ Φ i ]) → c i p' u ≡ c i (g i (h i p')) u
      body u =
        proof:
          c i p' u
            ≡[ OI-elim-dep {B = λ u → c i p' u ≡ pAsC i (h i p') u} (cases p') u ]≡ 
          pAsC i (h i p') u
            ≡[ (let ss = unstrStr {Φ = Φ} {A = C} {B = λ _ → P I} f' i in let rr = cong (λ g → fst g u) (appCong (symm ss)) in rr) ]≡
          c i (g i (h i p')) u
        qed
          where
            cases : {i : Int}(p' : P' i)(v : (i ≡ O) ⊎ (i ≡ I)) → c i p' ∣ v ∣ ≡ pAsC i (h i p') ∣ v ∣
            cases p' (inl refl) =
                proof:
                 c O p' ∣ inl refl ∣
                   ≡[ symm (a~faAtO (c O p' ∣ inl refl ∣)) ]≡
                 a~fa (c O p' ∣ inl refl ∣) O
                   ≡[ snd (hRaw O p') ∣ inl refl ∣ ]≡
                 h O p'
                   ≡[ refl ]≡
                 pAsC O (h O p') ∣ inl refl ∣
                qed
            cases p' (inr refl) =
                proof:
                 c I p' ∣ inr refl ∣
                   ≡[ snd (hRaw I p') ∣ inr refl ∣ ]≡
                 h I p'
                   ≡[ refl ]≡
                 pAsC I (h I p') ∣ inr refl ∣
                qed

    qij : (i j : Int)(p' : P' i) → [ Φ i ∨ Φ j ] → Π (P ∘ max i)
    qij i j p' = OI-elim' (qi i p') (qj i j p') (corners p') where
      qi : (i : Int)(p' : P' i) → (i ≡ O) ⊎ (i ≡ I) → Π (P ∘ max i)
      qi i p' x = q' i p' ∣ x ∣
      qj : (i j : Int)(p' : P' i) → (j ≡ O) ⊎ (j ≡ I) → Π (P ∘ max i)
      qj i .O p' (inl refl) = fst (gPath i (h i p'))
      qj i .I p' (inr refl) = fst (hPath i p')
      corners : {i j : Int}(p' : P' i)(e e' : OI) (i≡e : i ≡ ⟨ e ⟩) (j≡e' : j ≡ ⟨ e' ⟩) → qi i p' (OIinj i e i≡e) ≡ qj i j p' (OIinj j e' j≡e')
      corners {i} p' e O' i≡e refl = primTrustMe --fst (snd (hFiller i p')) ∣ OIinj i e i≡e ∣
      corners p' O' I' refl refl = primTrustMe
        -- proof:
        --   qi O p' (OIinj O O' refl) 
        --     ≡[ refl ]≡
        --   a~fa (c O p' ∣ inl refl ∣)
        --     ≡[  cong a~fa (symm (hO≡cO p'))  ]≡
        --   a~fa (h O p')
        --     ≡[ refl ]≡
        --   q O (h O p') ∣ inl refl ∣
        --     ≡[ fst (snd (gFiller O (h O p'))) ∣ inl refl ∣ ]≡
        --   fst (gPath O (h O p'))
        -- qed
      corners p' I' I' refl refl = primTrustMe
        -- proof:
        --   qi I p' (OIinj I I' refl) 
        --     ≡[ cong (λ p → (λ _ → p)) (snd (hRaw I p') ∣ inr refl ∣) ]≡
        --   (λ _ → h I p')
        --     ≡[ fst (snd (gFiller I (h I p'))) ∣ inr refl ∣ ]≡
        --   fst (gPath I (h I p'))
        -- qed

    pathBRaw : {i : Int}(p' : P' i)(j : Int) → ⟦ p ∈ (P I) ∣ (Φ i ∨ Φ j , qij i j p') ∙ I ↗ p ⟧
    pathBRaw {i} p' j = ρ O' (max i) (Φ i ∨ Φ j) (qij i j p') (h i p' , extends) where -- [ Φ i ∨ Φ j ] → Π (P ∘ max i)
      extends : prf ((Φ i ∨ Φ j , qij i j p') ∙ O ↗ h i p')
      extends u = or-elim-eq (λ u → qij i j p' u O) (h i p')
        (λ {l} → OI-elim-dep {B = Bi} (iCase p') l) ((λ {r} → OI-elim-dep {B = Bj} (jCase p') r)) u where
          Bi : [ Φ i ] → Set
          Bi u = qij i j p' ∣ inl u ∣ O ≡ h i p'
          iCase : {i : Int}(p' : P' i)(u : (i ≡ O) ⊎ (i ≡ I)) → qij i j p' ∣ inl ∣ u ∣ ∣ O ≡ h i p'
          iCase p' (inl refl) = snd (hRaw O p') ∣ inl refl ∣
          iCase p' (inr refl) = snd (hRaw I p') ∣ inr refl ∣
          Bj : [ Φ j ] → Set
          Bj u = qij i j p' ∣ inr u ∣ O ≡ h i p'
          jCase : {i j : Int}(p' : P' i)(u : (j ≡ O) ⊎ (j ≡ I)) → qij i j p' ∣ inr ∣ u ∣ ∣ O ≡ h i p'
          jCase {i} p' (inr refl) = fst (snd (hPath i p')) 
          jCase {i} p' (inl refl) = fst (snd (gPath i (h i p'))) 
    pathB : {i : Int}(p' : P' i) → Int → P I
    pathB {i} p' j = fst (pathBRaw p' j)
    extends : (j : Int)(x : [ Φ i ]) → f' i x (c i p' x) ≡ pathB p' j
    extends j u = OI-elim-dep {B = λ x → f' i x (c i p' x) ≡ pathB p' j} (cases p') u where
      cases : {i : Int}(p' : P' i)(v : (i ≡ O) ⊎ (i ≡ I)) → f' i ∣ v ∣ (c i p' ∣ v ∣) ≡ pathB p' j
      cases p' (inl refl) = primTrustMe -- For speed, real proof: snd (pathBRaw p' j) ∣ inl ∣ inl refl ∣ ∣
      cases p' (inr refl) = primTrustMe -- For speed, real proof: snd (pathBRaw p' j) ∣ inl ∣ inr refl ∣ ∣
    path : Int → P' i
    path j = str {Φ = Φ} {A = C} {B = λ _ → P I} f' i (c i p' , pathB p' j , extends j)

    pathBAtO : pathB p' O ≡ b i (g i (h i p'))
    pathBAtO =
      proof:
        pathB p' O
          ≡[ (let rr = snd (pathBRaw p' O) ∣ inr ∣ inl refl ∣ ∣ in symm rr) ]≡
        fst (gPath i (h i p')) I
          ≡[ snd (snd (gPath i (h i p'))) ]≡
        b i (g i (h i p'))
      qed
    pathO≡ghp' : path O ≡ g i (h i p')
    pathO≡ghp' = 
      proof:
        path O
          ≡[ cong (str {Φ = Φ} {A = C} {B = λ _ → P I} f' i)
              (glueExt {Φ = Φ} {A = C} {B = λ _ → P I} f' ((c i p' , pathB p' O , extends O))
                 (unstr {Φ = Φ} {A = C} {B = λ _ → P I} f' i (g i (h i p'))) fstEq pathBAtO)
            ]≡
        str {Φ = Φ} {A = C} {B = λ _ → P I} f' i (unstr {Φ = Φ} {A = C} {B = λ _ → P I} f' i (g i (h i p')))   
          ≡[ appCong (strUnstr {Φ = Φ} {A = C} {B = λ _ → P I} f' i) ]≡ 
        g i (h i p')
      qed
    
    pathBAtI : pathB p' I ≡ b i p'
    pathBAtI =
      proof:
        pathB p' I
          ≡[ (let rr = snd (pathBRaw p' I) ∣ inr ∣ inr refl ∣ ∣ in symm rr) ]≡
        fst (hPath i p') I
          ≡[ snd (snd (hPath i p')) ]≡
        b i p'
      qed
    pathI≡p' : path I ≡ p'
    pathI≡p' = 
      proof:
        path I
          ≡[ cong (str {Φ = Φ} {A = C} {B = λ _ → P I} f' i)
              (glueExt {Φ = Φ} {A = C} {B = λ _ → P I} f' ((c i p' , pathB p' I , extends I))
                 (unstr {Φ = Φ} {A = C} {B = λ _ → P I} f' i p') refl pathBAtI)
            ]≡ 
        str {Φ = Φ} {A = C} {B = λ _ → P I} f' i (unstr {Φ = Φ} {A = C} {B = λ _ → P I} f' i p')   
          ≡[ appCong (strUnstr {Φ = Φ} {A = C} {B = λ _ → P I} f' i) ]≡
        p'
      qed
      
  result : Fib P' → IdU (P i) (P' i)
  result ρ' = fst (equivToId {α = ρi} {β = ρ'i} (g i) (qinv2equivSimple (λ e p → ρ e (λ _ → i)) (λ e p → ρ' e (λ _ → i)) (g i) (h i , ghInv , hgInv))) where
    ρi : Fib (λ _ → P i)
    ρi e p = ρ e (λ _ → i)
    ρ'i : Fib (λ _ → P' i)
    ρ'i e p = ρ' e (λ _ → i)
