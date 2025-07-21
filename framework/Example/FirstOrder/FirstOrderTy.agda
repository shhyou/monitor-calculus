{-# OPTIONS --without-K --safe #-}

open import Annotation.Language

module Example.FirstOrder.FirstOrderTy (𝒜 : AnnTerm) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Product.Base as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_ ; _,′_)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template

open AnnTerm 𝒜 using (Ann; State)

private variable
  Δ Δ′ : TCtxt
  Γ Γ′ : Ctxt
  τ τ′ τ₁ τ₂ τₐ τᵣ : TyN Δ
  e e′ ez es e₁ e₂ eₐ v : Ann ∣ Γ ⊢ τ

data FlatTy : (Δ : TCtxt) → (τ : TyN Δ) → Set where
  `/f_   : (a : tt ∈ Δ) → FlatTy Δ (` a)
  1/f    : FlatTy Δ `1
  ℕ/f    : FlatTy Δ `ℕ
  _*/f_  : FlatTy Δ τ₁ → FlatTy Δ τ₂ → FlatTy Δ (τ₁ `* τ₂)
  _+/f_  : FlatTy Δ τ₁ → FlatTy Δ τ₂ → FlatTy Δ (τ₁ `+ τ₂)
  μ/f_   : FlatTy (tt ∷ Δ) τ → FlatTy Δ (μ τ)

data FirstOrderTy : (τ : Ty) → Set where
  flat/fo : FlatTy [] τ → FirstOrderTy τ
  box/fo  : FirstOrderTy τ → FirstOrderTy (Box τ)
  _→/fo_  : (τₐ/ft : FlatTy [] τₐ) → FirstOrderTy τᵣ → FirstOrderTy(τₐ `→ τᵣ)


ft0mapsto [ft0↦_] :
  FlatTy Δ τ →
  (a : tt ∈ (tt ∷ Δ)) → FlatTy Δ ([t0↦ τ ] a)
ft0mapsto τ/ft (here refl)  = τ/ft
ft0mapsto τ/ft (there x∈Δ) = `/f x∈Δ
[ft0↦_] = ft0mapsto

ftrename :
  FlatTy Δ τ →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  FlatTy Δ′ (trename τ ren)
ftrename (`/f a)           ren = `/f (ren a)
ftrename 1/f               ren = 1/f
ftrename ℕ/f               ren = ℕ/f
ftrename (τ₁/ft */f τ₂/ft) ren = (ftrename τ₁/ft ren) */f (ftrename τ₂/ft ren)
ftrename (τ₁/ft +/f τ₂/ft) ren = (ftrename τ₁/ft ren) +/f (ftrename τ₂/ft ren)
ftrename (μ/f τ/ft)        ren = μ/f (ftrename τ/ft (pext ren))

ftext :
  {σ : tt ∈ Δ → TyN Δ′} →
  (σf : (a : tt ∈ Δ) → FlatTy Δ′ (σ a)) →
  (a : tt ∈ (tt ∷ Δ)) → FlatTy (tt ∷ Δ′) (text σ a)
ftext σf (here refl) = `/f (here refl)
ftext σf (there x∈Δ) = ftrename (σf x∈Δ) there

ftsubst :
  FlatTy Δ τ →
  {σ : tt ∈ Δ → TyN Δ′} →
  (σf : (a : tt ∈ Δ) → FlatTy Δ′ (σ a)) →
  FlatTy Δ′ (tsubst τ σ)
ftsubst (`/f a)           σf = σf a
ftsubst 1/f               σf = 1/f
ftsubst ℕ/f               σf = ℕ/f
ftsubst (τ₁/ft */f τ₂/ft) σf = (ftsubst τ₁/ft σf) */f (ftsubst τ₂/ft σf)
ftsubst (τ₁/ft +/f τ₂/ft) σf = (ftsubst τ₁/ft σf) +/f (ftsubst τ₂/ft σf)
ftsubst (μ/f τ/ft)        σf = μ/f (ftsubst τ/ft (ftext σf))
