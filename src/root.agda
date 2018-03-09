----------------------------------------------------------------------
-- For CSL Special Issue reviewers:
--
-- In the process of checking the proofs from the paper in Agda we
-- have found a few small typos/mistakes. These are all easily fixible
-- They are:
--
-- - In Theorem 7.3 the final target of f' should be B x, not simply B
--
--
-- - In Theorem 7.4 the type of coerce should be:
--
--     {Γ : Set}{A B : Fib Γ} → IdU A B → (x : Γ) → A x → B x
--
--   rather than:
--
--     {Γ : Set}{A B : Fib Γ} → IdU A B → A → B
--
--
-- - At the end of Theorem 7.4 we claim that:
--
--     coerce (equivToPath f e) x a = trivComp B O x a
--
--   when in fact this should be:
--
--     coerce (equivToPath f e) x a = trivComp B I x (trivComp B O x a)
--
--   This does not affect the final result since a is still path equal
--   to two trivial comopositions starting at a. The correct statement
--   and its proof can be found in the univalence module of this Agda.
--
----------------------------------------------------------------------

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

module root where

----------------------------------------------------------------------
-- Introducing basics (e.g. equality, products etc)
----------------------------------------------------------------------
open import prelude

----------------------------------------------------------------------
-- Impredicative universe of propositions and logic
----------------------------------------------------------------------
open import impredicative 

----------------------------------------------------------------------
-- The interval I
----------------------------------------------------------------------
open import interval

----------------------------------------------------------------------
-- Cofibrant propositions
----------------------------------------------------------------------
open import cof

----------------------------------------------------------------------
-- Fibrations
----------------------------------------------------------------------
open import fibrations

----------------------------------------------------------------------
-- Type formers: products, functions, path and identity types
----------------------------------------------------------------------
open import Data.products
open import Data.functions
open import Data.paths
open import Data.id

----------------------------------------------------------------------
-- Equivalences, quasi-inverss, contractiability, extendability etc
----------------------------------------------------------------------
open import equivs

----------------------------------------------------------------------
-- The glueing construction
----------------------------------------------------------------------
open import glueing

----------------------------------------------------------------------
-- Univalence 
----------------------------------------------------------------------
open import univalence
