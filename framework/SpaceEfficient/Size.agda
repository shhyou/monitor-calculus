{-# OPTIONS --safe --without-K #-}

open import Annotation.Language

module SpaceEfficient.Size (Label : Set) (𝒜 : AnnTerm) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s; _⊔_)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_; ∃₂)

open import Data.List.Base as List using (List; []; _∷_; length; map)

open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Syntax.Type
open import Syntax.Term

open import Contract.Common Label
open import Contract.Base Label 𝒜  using (SCtc1N; SCtc1; flat)
open import SpaceEfficient.Base Label 𝒜

open AnnTerm 𝒜 using (Ann; State)

private variable
  Δ : TCtxt
  Γ : Ctxt
  τ τ′ τ₁ τ₂ τₐ τᵣ : TyN Δ

sectc-size : ∀ {Δ τ} → SECtcN Δ τ → ℕ
sectc-size (` a)           = 1
sectc-size 1/cc            = 1
sectc-size (flat/cc preds) = length preds
sectc-size (cκ₁ */cc cκ₂)  = suc (sectc-size cκ₁ + sectc-size cκ₂)
sectc-size (cκ₁ +/cc cκ₂)  = suc (sectc-size cκ₁ + sectc-size cκ₂)
sectc-size (box/cc cκ)     = suc (sectc-size cκ)
sectc-size (cκₐ →/cc cκᵣ)  = suc (sectc-size cκₐ + sectc-size cκᵣ)
sectc-size (μ/cc cκ)       = suc (sectc-size cκ)

leaf-size : ∀ {Δ τ} → SECtcN Δ τ → ℕ
leaf-size (` a)           = 0
leaf-size 1/cc            = 0
leaf-size (flat/cc preds) = length preds
leaf-size (cκ₁ */cc cκ₂)  = leaf-size cκ₁ ⊔ leaf-size cκ₂
leaf-size (cκ₁ +/cc cκ₂)  = leaf-size cκ₁ ⊔ leaf-size cκ₂
leaf-size (box/cc cκ)     = leaf-size cκ
leaf-size (cκₐ →/cc cκᵣ)  = leaf-size cκₐ ⊔ leaf-size cκᵣ
leaf-size (μ/cc cκ)       = leaf-size cκ

module _ (𝒜view : AnnTermView 𝒜 𝒜cctc) where
  program-size : Ann ∣ Γ ⊢ τ → ℕ
  program-size (proxy {e = e} A em) = suc (sectc-size (AnnTermView.getAnn 𝒜view A) + program-size e)
  program-size (B# A ⟪ e ⟫)         = suc (sectc-size (AnnTermView.getAnn 𝒜view A) + program-size e)
  program-size ⋆                    = 1
  program-size `z                   = 1
  program-size (`s e)               = suc (program-size e)
  program-size (foldN e ez es)      = suc (program-size e + (program-size ez + program-size es))
  program-size (assert e)           = suc (program-size e)
  program-size (e₁ `, e₂)           = suc (program-size e₁ + program-size e₂)
  program-size (π₁ e)               = suc (program-size e)
  program-size (π₂ e)               = suc (program-size e)
  program-size (inl e)              = suc (program-size e)
  program-size (inr e)              = suc (program-size e)
  program-size (case e of e₁ ∣ e₂)  = suc (program-size e + (program-size e₁ + program-size e₂))
  program-size (box e)              = suc (program-size e)
  program-size (unbox e)            = suc (program-size e)
  program-size (` y)                = 1
  program-size (ƛ e)                = suc (program-size e)
  program-size (e · eₐ)             = suc (program-size e + program-size eₐ)
  program-size (unroll e)           = suc (program-size e)
  program-size (roll τ e)           = suc (program-size e)
  program-size (fix e)              = suc (program-size e)
  program-size (e ⨟ e₁)             = suc (program-size e + program-size e₁)
