{-# OPTIONS --safe --without-K #-}

module Example.Unit.Annotation where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)

open import Syntax.Type
open import Syntax.Term
open import Annotation.Language

𝒜unit : AnnTerm
AnnTerm.Ann   𝒜unit τ = ⊤
AnnTerm.State 𝒜unit = ⊤

𝒜unit-terminal : {𝒜 : AnnTerm} → AnnTermView 𝒜 𝒜unit
𝒜unit-terminal {𝒜} = mkView (λ A → tt)
                            (λ s → tt)
                            (λ tt s → s)
                            (λ s → refl)
                            (λ s tt → refl)
                            (λ s tt tt′ → refl)
