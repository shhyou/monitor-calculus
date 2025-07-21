{-# OPTIONS --without-K --safe #-}

open import Annotation.Language

module SpaceEfficient.NonRecursive (Label : Set) (𝒜 : AnnTerm) where

open import Data.Unit.Base as Unit using (⊤; tt)

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Syntax.Type
open import Syntax.Term

open import Contract.Common Label
open import Contract.Base Label 𝒜
  using (SCtc1N; SCtc1; flat; flat-pred)
open import SpaceEfficient.Base Label 𝒜

private variable
  τ τ₁ τ₂ τₐ τᵣ : Ty

data SECtcNonRecursive : ∀ {τ} → SECtc τ → Set where
  1/nr :
    SECtcNonRecursive 1/cc
  flat/nr : ∀ {preds : List (SCtc1 `ℕ)} →
    SECtcNonRecursive (flat/cc preds)
  _*/nr_  : ∀ {cκ₁ cκ₂} →
    SECtcNonRecursive cκ₁ →
    SECtcNonRecursive cκ₂ →
    SECtcNonRecursive {τ₁ `* τ₂} (cκ₁ */cc cκ₂)
  _+/nr_  : ∀ {cκ₁ cκ₂} →
    SECtcNonRecursive cκ₁ →
    SECtcNonRecursive cκ₂ →
    SECtcNonRecursive {τ₁ `+ τ₂} (cκ₁ +/cc cκ₂)
  box/nr  : ∀ {cκ} →
    SECtcNonRecursive cκ →
    SECtcNonRecursive {Box τ} (box/cc cκ)
  _→/nr_  : ∀ {cκₐ cκᵣ} →
    SECtcNonRecursive cκₐ →
    SECtcNonRecursive cκᵣ →
    SECtcNonRecursive {τₐ `→ τᵣ} (cκₐ →/cc cκᵣ)

cnr-*₁ : ∀ {cκ} →
  SECtcNonRecursive {τ₁ `* τ₂} cκ → SECtcNonRecursive (*/cc-cκ₁ cκ)
cnr-*₁ (cnr₁ */nr cnr₂) = cnr₁

cnr-*₂ : ∀ {cκ} →
  SECtcNonRecursive {τ₁ `* τ₂} cκ → SECtcNonRecursive (*/cc-cκ₂ cκ)
cnr-*₂ (cnr₁ */nr cnr₂) = cnr₂

cnr-+₁ : ∀ {cκ} →
  SECtcNonRecursive {τ₁ `+ τ₂} cκ → SECtcNonRecursive (+/cc-cκ₁ cκ)
cnr-+₁ (cnr₁ +/nr cnr₂) = cnr₁

cnr-+₂ : ∀ {cκ} →
  SECtcNonRecursive {τ₁ `+ τ₂} cκ → SECtcNonRecursive (+/cc-cκ₂ cκ)
cnr-+₂ (cnr₁ +/nr cnr₂) = cnr₂

cnr-box : ∀ {cκ} →
  SECtcNonRecursive {Box τ} cκ → SECtcNonRecursive (box/cc-cκ cκ)
cnr-box (box/nr cnr) = cnr

cnr-dom : ∀ {cκ} →
  SECtcNonRecursive {τₐ `→ τᵣ} cκ → SECtcNonRecursive (→/cc-dom-cκ cκ)
cnr-dom (cnrₐ →/nr cnrᵣ) = cnrₐ

cnr-rng : ∀ {cκ} →
  SECtcNonRecursive {τₐ `→ τᵣ} cκ → SECtcNonRecursive (→/cc-rng-cκ cκ)
cnr-rng (cnrₐ →/nr cnrᵣ) = cnrᵣ
