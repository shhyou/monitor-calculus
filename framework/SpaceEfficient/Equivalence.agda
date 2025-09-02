{-# OPTIONS --safe --without-K #-}

module SpaceEfficient.Equivalence (Level : Set) where

open import Annotation.Language

open import SpaceEfficient.Equivalence.Base Level public

open import SpaceEfficient.OrderedPredicate Level 𝒜csctc

module _ (OP : OrderedPredicate (AnnTermView.getState 𝒜sctc-view) (AnnTermView.putState 𝒜sctc-view)) where
  open import SpaceEfficient.Equivalence.OpSemantics Level (OrderedPredicate.stronger? OP) public
  open import SpaceEfficient.Equivalence.Simulation Level OP public
  open import SpaceEfficient.Equivalence.Invariant Level OP public
  open import SpaceEfficient.Equivalence.Soundness Level OP public
