----------------------------------------------------------------------
-- This Agda code is an experiment with building universes internally
--
-- The idea for getting an impredicative universe of propositions Ω
-- comes from Martin Escardo, more details can be found at:
--
--          http://www.cs.bham.ac.uk/~mhe/impredicativity/
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module Data.universe-ua where

open import prelude
open import impredicative
open import cof
open import interval
open import fibrations
open import equivs
open import Data.paths

data U : Set₁ where
  u : (Γ :{♭} Set)(A :{♭} Fib Γ) → Γ → U

El : U → Set
El (u _ (A , _) x) = A x

el : isFib El
el e p = ρ e id where
  ρ : isFib (El ∘ p)
  ρ e' p' φ f x = {!!}


code : {Γ :{♭} Set}(A :{♭} Fib Γ) → (Γ → U)
code {Γ} A x = u Γ A x

decode : ∀{a}{Γ : Set a} → (Γ → U) → Fib Γ
decode = reindex' (El , el)

code-el  : {Γ :{♭} Set}(A :{♭} Fib Γ) → decode (code A) ≡ A
code-el A = Σext refl refl

ctx : U → Set
ctx (u Γ _ _) = Γ

fib : (A : U) → Fib (ctx A)
fib (u _ A _) = A

base : (A : U) → ctx A
base (u _ _ x) = x

_=U=_ : U → U → Set₁
A =U= B = (f : Σ f ∈ (ctx A → ctx B) , f (base A) ≡ base B) → reindex' (fib B) (fst f) ≡ fib A
--(u Γ A x) =U= (u Δ B y) = (f : Σ f ∈ (Γ → Δ) , f x ≡ y) → (reindex' B (fst f) ≡ A)

code-el' : {Γ :{♭} Set}(a :{♭} Γ → U) → (x : Γ) → code (decode a) x =U= a x
code-el' a x (f , p) with a x
code-el' a x (f , refl) | u Δ B .(f x) = Σext {!!} {!!}
