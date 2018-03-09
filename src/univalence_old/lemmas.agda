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
module univalence.lemmas where

open import prelude
open import fibrations
open import equivs

open import glueing.core using (res; i=OI; <_,id>; compOI) public
open import glueing.core renaming
  ( FibGlue to FibGlueOrig
  )
open import glueing.strict renaming
  ( FibSGlue' to FibSGlue'Orig
  ; uaβhelper2 to uaβhelper2Orig
  ; str to strOrig
  ; unstr to unstrOrig
  ; strictness to strictnessOrig
  )
open import glueing.fix renaming (SGlueFib to SGlueFibOrig; uaβhelper to uaβhelperOrig)
open import univalence.core using
  (IdU; idToEquiv; makeC; makeF'; f'isEquiv; want) public
  
open import univalence.core renaming (equivToId to equivToIdOrig; uaβhelper4 to uaβhelper4Orig) 


SGlueFib = SGlueFibOrig

abstract
   uaβhelper = uaβhelperOrig
   FibSGlue' = FibSGlue'Orig
   uaβhelper2 = uaβhelper2Orig
   str = strOrig
   unstr = unstrOrig
   FibGlue = FibGlueOrig
   strictness = strictnessOrig
   equivToId = equivToIdOrig
   uaβhelper4 : {Γ : Set}{A B : Fib Γ}
     (f : (x : Γ) → fst A x → fst B x)(equiv : Equiv f)
     → want {Γ} {A} {B} f (equivToId {Γ} {A} {B} f equiv)
   uaβhelper4 = uaβhelper4Orig
