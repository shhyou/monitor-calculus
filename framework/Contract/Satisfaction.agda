{-# OPTIONS --without-K --safe #-}

open import Annotation.Language

module Contract.Satisfaction (Label : Set) (𝒜 : AnnTerm) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Syntax.Type
open import Syntax.Term
open import Annotation.Interpretation.Base
open import Contract.Base Label 𝒜

open AnnTerm 𝒜 using (Ann; State)

private variable
  Δ Δ′ : TCtxt
  τ τ₁ τ₂ τₐ τᵣ : TyN Δ

  𝒯 : AnnTransit 𝒜

data SCtcSat {𝒯} (ℐ : AnnIntr {𝒜} 𝒯) (ix : AIIx ℐ) : ∀ {Δ τ} → SCtc1N Δ τ → Set where
  `_ : ∀ a →
    SCtcSat ℐ ix {Δ} (` a)
  1/s :
    SCtcSat ℐ ix {Δ} 1/c
  flat/s : ∀ {l e} →
    (esat : ℐ ⊨[ ix ] e) →
    SCtcSat ℐ ix {Δ} (flat l e)
  _*/s_ : ∀ {sκ₁ sκ₂} →
    SCtcSat ℐ ix                sκ₁ →
    SCtcSat ℐ ix                sκ₂ →
    SCtcSat ℐ ix {Δ} {τ₁ `* τ₂} (sκ₁ */c sκ₂)
  _+/s_ : ∀ {sκ₁ sκ₂} →
    SCtcSat ℐ ix                sκ₁ →
    SCtcSat ℐ ix                sκ₂ →
    SCtcSat ℐ ix {Δ} {τ₁ `+ τ₂} (sκ₁ +/c sκ₂)
  box/s : ∀ {sκ} →
    SCtcSat ℐ ix             sκ →
    SCtcSat ℐ ix {Δ} {Box τ} (box/c sκ)
  _→/s_ : ∀ {sκₐ sκᵣ} →
    SCtcSat ℐ ix                sκₐ →
    SCtcSat ℐ ix                sκᵣ →
    SCtcSat ℐ ix {Δ} {τₐ `→ τᵣ} (sκₐ →/c sκᵣ)
  μ/s_ : ∀ {sκ} →
    SCtcSat ℐ ix           sκ →
    SCtcSat ℐ ix {Δ} {μ τ} (μ/c sκ)

sκsatrename : ∀ {ℐ : AnnIntr 𝒯} {ix} →
  {sκ : SCtc1N Δ τ} →
  SCtcSat ℐ ix sκ →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  SCtcSat ℐ ix (sκrename sκ ren)
sκsatrename (` a)               ren = ` (ren a)
sκsatrename 1/s                 ren = 1/s
sκsatrename (flat/s esat)       ren = flat/s esat
sκsatrename (sκsat₁ */s sκsat₂) ren = sκsatrename sκsat₁ ren */s sκsatrename sκsat₂ ren
sκsatrename (sκsat₁ +/s sκsat₂) ren = sκsatrename sκsat₁ ren +/s sκsatrename sκsat₂ ren
sκsatrename (box/s sκsat)       ren = box/s (sκsatrename sκsat ren)
sκsatrename (sκsatₐ →/s sκsatᵣ) ren = sκsatrename sκsatₐ ren →/s sκsatrename sκsatᵣ ren
sκsatrename (μ/s sκsat)         ren = μ/s (sκsatrename sκsat (pext ren))

sκsatext : ∀ {ℐ : AnnIntr 𝒯} {ix} →
  {σ : tt ∈ Δ → TyN Δ′} →
  {σκ : (a : tt ∈ Δ) → SCtc1N Δ′ (σ a)} →
  (σs : (a : tt ∈ Δ) → SCtcSat ℐ ix (σκ a)) →
  (a : tt ∈ (tt ∷ Δ)) → SCtcSat ℐ ix {tt ∷ Δ′} (sκext σκ a)
sκsatext σs (here refl)  = ` here refl
sκsatext σs (there x∈Δ) = sκsatrename (σs x∈Δ) there

sκsatsubst : ∀ {ℐ : AnnIntr 𝒯} {ix} →
  {σ : tt ∈ Δ → TyN Δ′} →
  {σκ : (a : tt ∈ Δ) → SCtc1N Δ′ (σ a)} →
  {sκ : SCtc1N Δ τ} →
  SCtcSat ℐ ix sκ →
  (σs : (a : tt ∈ Δ) → SCtcSat ℐ ix (σκ a)) →
  SCtcSat ℐ ix (sκsubst sκ σκ)
sκsatsubst (` a)               σs = σs a
sκsatsubst 1/s                 σs = 1/s
sκsatsubst (flat/s esat)       σs = flat/s esat
sκsatsubst (sκsat₁ */s sκsat₂) σs = sκsatsubst sκsat₁ σs */s sκsatsubst sκsat₂ σs
sκsatsubst (sκsat₁ +/s sκsat₂) σs = sκsatsubst sκsat₁ σs +/s sκsatsubst sκsat₂ σs
sκsatsubst (box/s sκsat)       σs = box/s (sκsatsubst sκsat σs)
sκsatsubst (sκsatₐ →/s sκsatᵣ) σs = sκsatsubst sκsatₐ σs →/s sκsatsubst sκsatᵣ σs
sκsatsubst (μ/s sκsat)         σs = μ/s (sκsatsubst sκsat (sκsatext σs))


sκsat0mapsto [sκsat0↦_] : ∀ {ℐ : AnnIntr 𝒯} {ix} {sκ : SCtc1N Δ τ} →
  SCtcSat ℐ ix {Δ} sκ →
  (a : tt ∈ (tt ∷ Δ)) →
  SCtcSat ℐ ix {Δ} ([sκ0↦ sκ ] a)
sκsat0mapsto sκsat (here refl) = sκsat
sκsat0mapsto sκsat (there x∈Δ) = ` x∈Δ

[sκsat0↦_] = sκsat0mapsto


sκsat-*₁ : ∀ {ℐ : AnnIntr 𝒯} {ix sκ} →
  SCtcSat ℐ ix {Δ} {τ₁ `* τ₂} sκ → SCtcSat ℐ ix (*/c-sκ₁ sκ)
sκsat-*₁ (sκsat₁ */s sκsat₂) = sκsat₁

sκsat-*₂ : ∀ {ℐ : AnnIntr 𝒯} {ix sκ} →
  SCtcSat ℐ ix {Δ} {τ₁ `* τ₂} sκ → SCtcSat ℐ ix (*/c-sκ₂ sκ)
sκsat-*₂ (sκsat₁ */s sκsat₂) = sκsat₂

sκsat-+₁ : ∀ {ℐ : AnnIntr 𝒯} {ix sκ} →
  SCtcSat ℐ ix {Δ} {τ₁ `+ τ₂} sκ → SCtcSat ℐ ix (+/c-sκ₁ sκ)
sκsat-+₁ (sκsat₁ +/s sκsat₂) = sκsat₁

sκsat-+₂ : ∀ {ℐ : AnnIntr 𝒯} {ix sκ} →
  SCtcSat ℐ ix {Δ} {τ₁ `+ τ₂} sκ → SCtcSat ℐ ix (+/c-sκ₂ sκ)
sκsat-+₂ (sκsat₁ +/s sκsat₂) = sκsat₂

sκsat-box : ∀ {ℐ : AnnIntr 𝒯} {ix sκ} →
  SCtcSat ℐ ix {Δ} {Box τ} sκ → SCtcSat ℐ ix (box/c-sκ sκ)
sκsat-box (box/s sκsat) = sκsat

sκsat-dom : ∀ {ℐ : AnnIntr 𝒯} {ix sκ} →
  SCtcSat ℐ ix {Δ} {τₐ `→ τᵣ} sκ → SCtcSat ℐ ix (→/c-dom-sκ sκ)
sκsat-dom (sκsatₐ →/s sκsatᵣ) = sκsatₐ

sκsat-rng : ∀ {ℐ : AnnIntr 𝒯} {ix sκ} →
  SCtcSat ℐ ix {Δ} {τₐ `→ τᵣ} sκ → SCtcSat ℐ ix (→/c-rng-sκ sκ)
sκsat-rng (sκsatₐ →/s sκsatᵣ) = sκsatᵣ

sκsat-μ : ∀ {ℐ : AnnIntr 𝒯} {ix sκ} →
  SCtcSat ℐ ix {Δ} {μ τ} sκ →
  SCtcSat ℐ ix (μ/c-sκ sκ)
sκsat-μ (μ/s sκsat) = sκsatsubst sκsat [sκsat0↦ μ/s sκsat ]
