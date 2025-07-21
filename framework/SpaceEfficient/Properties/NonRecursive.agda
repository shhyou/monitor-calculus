{-# OPTIONS --without-K --safe #-}

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Data.Unit.Base as Unit using (⊤; tt)

open import Annotation.Language
open import SpaceEfficient.Base
  using ()
  renaming (𝒜cctc to SE𝒜cctc)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (Pred to SEPred)

module SpaceEfficient.Properties.NonRecursive
  (Label : Set)
  {𝒜 : AnnTerm}
  (𝒜cctc-view : AnnTermView 𝒜 (SE𝒜cctc Label 𝒜))
  (stronger? : SEPred Label 𝒜 → SEPred Label 𝒜 → Dec ⊤)
  where

open import Level using (0ℓ)

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; _++_; [_]; length; map)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Effect.Monad using (RawMonad)

open import Data.Tick using (Tick; evalTick; ✓_; monad)

open import Syntax.Type
open import Syntax.Term

open import Annotation.Language
open import Contract.Common Label
open import Contract.Base Label 𝒜
open SpaceEfficient.Base Label 𝒜
open import SpaceEfficient.NonRecursive Label 𝒜
open AnnTerm 𝒜 hiding (State)

open SECtcTransitSteps 𝒜cctc-view stronger?

cnr-join : ∀ {τ cκ′ cκ} →
  SECtcNonRecursive cκ′ →
  SECtcNonRecursive cκ →
  SECtcNonRecursive (evalTick (✓ join {τ = τ} cκ′ cκ))
cnr-join 1/nr               1/nr             = 1/nr
cnr-join flat/nr            flat/nr          = flat/nr
cnr-join (cnr₁′ */nr cnr₂′) (cnr₁ */nr cnr₂) = (cnr-join cnr₁′ cnr₁) */nr (cnr-join cnr₂′ cnr₂)
cnr-join (cnr₁′ +/nr cnr₂′) (cnr₁ +/nr cnr₂) = (cnr-join cnr₁′ cnr₁) +/nr (cnr-join cnr₂′ cnr₂)
cnr-join (box/nr cnr′)      (box/nr cnr)     = box/nr (cnr-join cnr′ cnr)
cnr-join (cnrₐ′ →/nr cnrᵣ′) (cnrₐ →/nr cnrᵣ) = (cnr-join cnrₐ cnrₐ′) →/nr (cnr-join cnrᵣ′ cnrᵣ)
