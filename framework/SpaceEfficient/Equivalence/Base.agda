{-# OPTIONS --safe --without-K #-}

module SpaceEfficient.Equivalence.Base (Label : Set) where

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_)

open import Function.Base using (const)

open import Syntax.Type
open import Syntax.Term
open import Annotation.Language

𝒜csctc : AnnTerm
open import Contract.Common Label
open import Contract.Base Label 𝒜csctc
open import SpaceEfficient.Base Label 𝒜csctc
open AnnTerm 𝒜csctc using (Ann; State)


AnnTerm.Ann   𝒜csctc τ = SECtcN [] τ × List (SCtc1N [] τ)
AnnTerm.State 𝒜csctc = Status × Status


𝒜sctc-view : AnnTermView 𝒜csctc 𝒜sctc
𝒜sctc-view = mkView proj₂
                    proj₂
                    (λ s → Product.map₂ (const s))
                    (λ s → refl)
                    (λ s₁ s₂ → refl)
                    (λ s₁ s₂ s₂′ → refl)


𝒜cctc-view : AnnTermView 𝒜csctc 𝒜cctc
𝒜cctc-view = mkView proj₁
                    proj₁
                    (λ s → Product.map₁ (const s))
                    (λ s → refl)
                    (λ s₁ s₂ → refl)
                    (λ s₁ s₂ s₂′ → refl)
