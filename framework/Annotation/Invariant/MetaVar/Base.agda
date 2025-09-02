{-# OPTIONS --without-K --safe #-}

module Annotation.Invariant.MetaVar.Base where

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import Annotation.Language
open import Annotation.Invariant.Base

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

private variable
  𝒜 : AnnTerm
  𝒯 : AnnTransit 𝒜

  Ψ : List Ty
  Δ : List (Ctxt × Ty)

  Γ : Ctxt
  τ τ₁ τ₂ : Ty

VarIx : (ℐ : AnnInvr {𝒜} 𝒯) → (Δ : List (Ctxt × Ty)) → Set
VarIx ℐ Δ = ∀ {x} → (y : x ∈ Δ) → AIIx ℐ

AnnIx : (ℐ : AnnInvr {𝒜} 𝒯) → (Ψ : List Ty) → Set
AnnIx ℐ Ψ = ∀ {τ} → (a : τ ∈ Ψ) → AIIx ℐ

record MetaVarIx (ℐ : AnnInvr {𝒜} 𝒯) (ϑ : MetaVar (ATAnn 𝒜) Ψ Δ) : Set where
    inductive; no-eta-equality; pattern
    constructor mkMVIx
    field
      varIxᵗ : VarIx ℐ Δ
      annCtxtIxᵗ : AnnIx ℐ Ψ
      annIxᵗ : AnnIx ℐ Ψ
open MetaVarIx public

MetaVarSat : (ℐ : AnnInvr {𝒜} 𝒯) → MEnv (ATAnn 𝒜) Δ → VarIx ℐ Δ → Set
MetaVarSat {Δ = Δ} ℐ termEnv varIx = ∀ {x} → (y : x ∈ Δ) → ℐ ⊨[ varIx y ] termEnv y

[ix↦_] : {A : Set} → A → ∀ {τ′} → (a : τ′ ∈ (τ ∷ [])) → A
[ix↦_] ix (here _) = ix

[ix0↦_&&ix1↦_] : {A : Set} → A → A → ∀ {τ′} → (a : τ′ ∈ (τ₁ ∷ τ₂ ∷ [])) → A
[ix0↦_&&ix1↦_] ix0 ix1 (here _)         = ix0
[ix0↦_&&ix1↦_] ix0 ix1 (there (here _)) = ix1

[ix0↦_&&ix1↦_&&ix2↦_] : {A : Set} → A → A → A → ∀ {τ′} → (a : τ′ ∈ (τ ∷ τ₁ ∷ τ₂ ∷ [])) → A
[ix0↦_&&ix1↦_&&ix2↦_] ix0 ix1 ix2 (here _)                 = ix0
[ix0↦_&&ix1↦_&&ix2↦_] ix0 ix1 ix2 (there (here _))         = ix1
[ix0↦_&&ix1↦_&&ix2↦_] ix0 ix1 ix2 (there (there (here _))) = ix2
