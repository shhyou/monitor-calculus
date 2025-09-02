{-# OPTIONS --without-K --safe #-}

module Annotation.Invariant.MetaVar where

open import Annotation.Invariant.MetaVar.Base public
open import Annotation.Invariant.MetaVar.Predicate public
open import Annotation.Invariant.MetaVar.View public
open import Annotation.Invariant.MetaVar.BoundaryPredicate public

-- Annotation.Invariant.MetaVar.View is included since it appears in the type
-- of the user interface (via Annotation.Invariant.Decompose and
-- Annotation.Invariant.Property
