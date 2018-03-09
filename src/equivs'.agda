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
module equivs' where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.products
open import Data.paths

----------------------------------------------------------------------
-- Contr and Ext
----------------------------------------------------------------------
Contr' : Set → Set
Contr' A = Σ a₀ ∈ A , ((a : A) → a₀ ~ a)

Contr : {Γ : Set} → (Γ → Set) → Set
Contr {Γ} A = (x : Γ) → Contr' (A x)

Ext' : Set → Set
Ext' A = (φ : Cof)(f : [ φ ] → A) → ⟦ a ∈ A ∣ (φ , f) ↗ a ⟧

Ext : {Γ : Set} → (Γ → Set) → Set
Ext {Γ} A = (x : Γ) → Ext' (A x)

contr2ext : {Γ : Set}{A : Γ → Set} → isFib A → Contr A → Ext A
contr2ext {Γ} {A} α ap x φ f = (fst a' , (λ u → trans (q u) (p u))) where
  a : A x
  a = fst (ap x)

  c : (a' : A x) → a ~ a'
  c = snd (ap x)

  path : [ φ ] → Int → A x
  path u = fst (c (f u))
  
  a' : ⟦ a' ∈ (A x) ∣ (φ , path) ∙ I ↗ a' ⟧
  a' = α O' (λ _ → x) φ path (a , (λ u → fst (snd (c (f u)))))

  p : (u : [ φ ]) → f u ≡ fst (c (f u)) I
  p u = symm (snd (snd (c (f u))))

  q : (u : [ φ ]) → fst (c (f u)) I ≡ fst a'
  q = snd a'

ext2fib : {Γ : Set}{A : Γ → Set} → Ext A → isFib A × Contr A
ext2fib {A = A} ext = ((λ e p φ f a → ext (p ⟨ ! e ⟩) φ (λ z → f z ⟨ ! e ⟩)) , c) where
  c : Contr A
  fst (c x) = fst (ext x cofFalse ∅-elim)
  fst (snd (c x) a) i = fst (ext x (i ≈I) (λ _ → a))
  fst (snd (snd (c x) a)) = cong (λ{(φ , f) → fst (ext x φ f)}) (Σext bothFalse bothElim) where
    bothFalse : O ≈I ≡ cofFalse
    bothFalse = Σext (propext O≠I ∅-elim) refl
    bothElim : subst (λ z → [ z ] → A x) bothFalse (λ _ → a) ≡ ∅-elim
    bothElim = funext (λ false → ∅-elim false)
  snd (snd (snd (c x) a)) = symm (snd (ext x (I ≈I) (λ _ → a)) refl)


Fiber : {A B : Set}(f : A → B)(b : B) → Set
Fiber {A} f b = Σ a ∈ A , f a ~ b

Equiv : {A B : Set}(f : A → B) → Set
Equiv {A} {B} f = (b : B) → Contr' (Fiber f b)


res : (Γ : Set)(Φ : Γ → Cof) → Set
res Γ Φ = Σ x ∈ Γ , [ Φ x ]

Glue :
  {Γ : Set}
  (Φ : Γ → Cof)
  (A : res Γ Φ → Set)
  (B : Γ → Set)
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  Γ → Set
Glue Φ A B f x = Σ a ∈ ((u : [ Φ x ]) → A (x , u)) , ⟦ b ∈ (B x) ∣ All u ∈ [ Φ x ] , f x u (a u) ≈ b ⟧

glueExt :
  {Γ : Set}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  {x : Γ}
  (g g' : Glue Φ A B f x)
  (p : fst g ≡ fst g')
  (q : fst (snd g) ≡ fst (snd g'))
  → ---------------
  g ≡ g'
glueExt _ (_ , _ , fa≡b) (_ , _ , fa≡b') refl refl =
  Σext refl (Σext refl (funext (λ u → uip (fa≡b u) (fa≡b' u))))

FibGlue'' :
  {Γ : Set}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv (f x v))
  → ---------------
  isFib A → isFib B → isFib (Glue Φ A B f)
FibGlue'' {Γ} {Φ} {A} {B} f equiv α β e p ψ q ((a , b , fa↗b) , ext) = (g₁ , ext') where
  x : Γ
  x = p ⟨ ! e ⟩
  ~a : [ ψ ] → (u : [ Φ x ]) → A (x , u)
  ~a v = fst (q v ⟨ ! e ⟩)
  ~b : [ ψ ] → B x
  ~b v = fst (snd (q v ⟨ ! e ⟩))
  f~a=~b : (v : [ ψ ])(u : [ Φ x ]) → f x u (~a v u) ≡ ~b v
  f~a=~b v = snd (snd (q v ⟨ ! e ⟩))
  
  qb : [ ψ ] → Π (B ∘ p)
  qb u i = fst (snd (q u i))
  b₁' : ⟦ b ∈ (B (p ⟨ ! e ⟩)) ∣ (ψ , qb) ∙ ⟨ ! e ⟩ ↗ b ⟧
  b₁' = β e p ψ qb (b , (λ u → cong (λ g → fst (snd g)) (ext u)))

  a₁'p' : (u : [ Φ x ])(v : [ ψ ]) → Fiber (f x u) (fst b₁')
  a₁'p' u v = (~a v u , reflPath' (trans (snd b₁' v) (f~a=~b v u)))

  σ : (u : [ Φ x ]) → isFib (Fiber (f x u))
  σ u = FibΣ {B = λ{ (b , a) → f x u a ~ b}}
    (reindex A α (λ _ → x , u))
    (reindex (Path B) (FibPath β) (λ{ (b , a) → (x , f x u a , b)}))

  ε : (u : [ Φ x ]) → Ext' (Fiber (f x u) (fst b₁'))
  ε u = contr2ext (σ u) (equiv x u) (fst b₁')

  a₁p : (u : [ Φ x ]) → ⟦ ap ∈ Fiber (f x u) (fst b₁') ∣ (ψ , a₁'p' u) ↗ ap ⟧
  a₁p u = ε u ψ (a₁'p' u)

  a₁ : ⟦ a ∈ ((u : [ Φ x ]) → A (x , u)) ∣ (ψ , λ v → ~a v) ↗ a ⟧
  a₁ = (λ u → fst (fst (a₁p u))) , (λ v → (funext (λ u → cong fst (snd (a₁p u) v))))

  ~b-∪-fa₁ : [ ψ ∨ Φ x ] → Int → B (p ⟨ ! e ⟩)
  ~b-∪-fa₁ u i = _∪_ {φ = ψ} {ψ = Φ x} ~b (λ u → fst (snd (fst (a₁p u))) i) {agree} u where
    agree : prf ((ψ , ~b) ⌣ (Φ x , (λ u → fst (snd (fst (a₁p u))) i)))
    agree v u =
      let p≡refl = cong (λ ap → fst (snd ap) i) (snd (a₁p u) v) in
      let refl≡ = reflPathEval ((trans (snd b₁' v) (f~a=~b v u))) i in
      trans p≡refl (trans (symm refl≡) (snd b₁' v))
      
  b₁ : ⟦ b ∈ (B x) ∣ (ψ ∨ Φ x , ~b-∪-fa₁) ∙ O ↗ b ⟧
  b₁ = β I' (λ _ → x) (ψ ∨ Φ x) ~b-∪-fa₁
    ((fst b₁') , (λ u →
      or-elim-eq (λ u → ~b-∪-fa₁ u I)
        (fst b₁') (λ {l} → snd b₁' l) (λ {r} → snd (snd (snd (fst (a₁p r))))) u))

  g₁ : Glue Φ A B f x
  g₁ = (fst a₁ , fst b₁ , (λ u → trans (snd b₁ ∣ inr u ∣) (symm (fst (snd (snd (fst (a₁p u))))))))

  ext' : prf ((ψ , q) ∙ ⟨ ! e ⟩ ↗ g₁)
  ext' v = glueExt {Φ = Φ} f (q v ⟨ ! e ⟩) g₁ (snd a₁ v) (snd b₁ ∣ inl v ∣)

∀i : (p : Int → Cof) → Cof
fst (∀i p) = All i ∈ Int , fst (p i)
snd (∀i p) = cof∀ (fst ∘ p) (λ i → snd (p i))

FibFix :
  {Γ : Set}
  {Φ : Γ → Cof}
  {G : Γ → Set}
  → ---------------
  isFib {Γ = res Γ Φ} (G ∘ fst) → isFib G → isFib G
FibFix {Γ} {Φ} {G} α γ e p ψ f (g , ext) = let g' = γ e p (ψ ∨ ∀i (Φ ∘ p)) f' (g , ext') in (fst g') , (λ u → snd g' ∣ inl u ∣) where
  aFill : (∀iΦ : [ ∀i (Φ ∘ p) ]) →
    ⟦ a' ∈ ((i : Int) → G (p i)) ∣
      ((ψ , f) ↗ a') & (a' ⟨ e ⟩ ≈ g) ⟧
  aFill ∀iΦ = fill {A = G ∘ fst} e α (λ i → (p i) , ∀iΦ i) ψ f g ext
  f' : [ ψ ∨ ∀i (Φ ∘ p) ] → Π (G ∘ p)
  f' = _∪_ {φ = ψ} {ψ = ∀i (Φ ∘ p)} f (λ u → fst (aFill u)) {λ v ∀Φi → fst (snd (aFill ∀Φi)) v}
  ext' : prf ((ψ ∨ ∀i (Φ ∘ p) , f') ∙ ⟨ e ⟩ ↗ g)
  ext' = or-elim-eq (λ u → f' u ⟨ e ⟩) g (λ {l} → ext l) (λ {r} → snd (snd (aFill r)))

FibFix' :
  {Γ : Set}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {G : Γ → Set}
  → ---------------
  A ≡ G ∘ fst → isFib A → isFib G → isFib G
FibFix' {Γ} {Φ} {A} {G} eq α γ = FibFix {Γ} {Φ} {G} (subst isFib eq α) γ
