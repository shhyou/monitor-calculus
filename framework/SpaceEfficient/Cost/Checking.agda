{-# OPTIONS --safe --without-K #-}

open import Annotation.Language

module SpaceEfficient.Cost.Checking (Label : Set) (𝒜 : AnnTerm) where

open import Relation.Nullary using (Dec; yes; no; _because_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; _*_; pred)
open import Data.Product as Product using (Σ; _,_; proj₁; proj₂)

open import Data.List.Base as List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Data.Tick using (Tick; execTick; ✓_)

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base

open import Contract.Common Label
open import Contract.Base Label 𝒜
  using (SCtc1N; flat)
open import SpaceEfficient.Base Label 𝒜
open import SpaceEfficient.OrderedPredicate Label 𝒜

open AnnTerm 𝒜 using (Ann; State)

import TransitionRelationUtil

private
  module TR = TransitionRelationUtil State

𝒜chkcost : AnnTerm
AnnTerm.Ann   𝒜chkcost τ = SECtcN [] τ
AnnTerm.State 𝒜chkcost = ℕ

module CheckingCostTransitSteps
    (𝒜view : AnnTermView 𝒜 𝒜chkcost)
    (𝒜cctc-view : AnnTermView 𝒜 𝒜cctc)
    (stronger? : Pred → Pred → Dec ⊤) where
  open SECtcTransitSteps 𝒜cctc-view stronger?
  open AnnTermViewUtils 𝒜view

  𝒯chkcost : AnnTransit 𝒜
  𝒯chkcost `R-cross-unit (_ , refl) (ϑ , tt) ψ ψ′ =
    TR.id
  𝒯chkcost `R-cross-nat (_ , refl) (ϑ , isval) ψ ψ′ =
    λ s s′ →
      getAnn[ cκ ← ψ(here refl) ]
        s′ ≡ putState (getState s + length (flat/cc-preds cκ)) s
  𝒯chkcost `R-cross-cons (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁ , isval₂) ψ ψ′ =
    TR.id
  𝒯chkcost `R-cross-inl (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁) ψ ψ′ =
    TR.id
  𝒯chkcost `R-cross-inr (_ , (τ₁ , τ₂) , refl) (ϑ , isval₂) ψ ψ′ =
    TR.id
  𝒯chkcost `R-cross-roll (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    TR.id
  𝒯chkcost `R-cross-box (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    TR.id
  𝒯chkcost `R-cross-lam (_ , (τₐ , τᵣ) , refl) (ϑ , tt) ψ ψ′ =
    TR.id
  𝒯chkcost `R-merge-box (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    TR.id
  𝒯chkcost `R-merge-lam (_ , (τₐ , τᵣ) , refl) (ϑ , tt) ψ ψ′ =
    TR.id
  𝒯chkcost `R-proxy-unbox (τ , tt) (ϑ , isval) ψ ψ′ =
    TR.id
  𝒯chkcost `R-proxy-β (τᵣ , τₐ) (ϑ , isval) ψ ψ′ =
    TR.id
