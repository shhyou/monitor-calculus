{-# OPTIONS --without-K --safe #-}

module Annotation.Interpretation.MetaVar where

open import Annotation.Interpretation.MetaVar.Base public
open import Annotation.Interpretation.MetaVar.Predicate public
open import Annotation.Interpretation.MetaVar.View public
open import Annotation.Interpretation.MetaVar.BoundaryPredicate public

-- Annotation.Interpretation.MetaVar.View is included since it appears in the type
-- of the user interface (via Annotation.Interpretation.Decompose and
-- Annotation.Interpretation.Property
