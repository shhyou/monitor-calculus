{-# OPTIONS --safe --without-K #-}

module SpaceEfficient.Bounded (Level : Set) where

open import Annotation.Language

open import SpaceEfficient.Bounded.Base Level public

open import SpaceEfficient.OrderedPredicate Level 𝒜ccctc

module _ (OP : OrderedPredicate (AnnTermView.getState 𝒜cctc-view) (AnnTermView.putState 𝒜cctc-view)) where
  open import SpaceEfficient.Bounded.OpSemantics Level (OrderedPredicate.stronger? OP) public
  open import SpaceEfficient.Bounded.Size Level 𝒜cctc-view OP public
    using (ℐsize; ℐsize-monotonic; ℐsize-sound)
  open import SpaceEfficient.Bounded.NonRecursiveHeight Level 𝒜cctc-view (OrderedPredicate.stronger? OP) public
    using (ℐnrheight; ℐnrheight-monotonic; ℐnrheight-sound)
  open import SpaceEfficient.Bounded.CheckingCost Level OP public
    using (check-cost-bounded; ℐchkbnd; check-bound; ℐchkbnd-monotonic; ℐchkbnd-sound)
  open import SpaceEfficient.Bounded.JoinCost Level OP public
    using (join-cost-bounded; ℐsebnd; se-c₀; join-bound; ℐsebnd-monotonic; ℐsebnd-sound)
