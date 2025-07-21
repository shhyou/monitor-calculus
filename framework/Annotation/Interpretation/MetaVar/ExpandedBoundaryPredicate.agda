{-# OPTIONS --without-K --safe #-}

module Annotation.Interpretation.MetaVar.ExpandedBoundaryPredicate where

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import Annotation.Language
open import Annotation.Interpretation.Base
open import Annotation.Interpretation.MetaVar.Base
open import Annotation.Interpretation.MetaVar.Predicate
open import Annotation.Interpretation.MetaVar.BoundaryPredicate
 renaming (IsSatIx to MVIsSatIx; BoundarySat to MVBoundarySat; IsTermIx to MVIsTermIx)

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; sym; trans)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)

private variable
  𝒜 : AnnTerm
  𝒯 : AnnTransit 𝒜

  Ψ : List Ty
  Δ : List (Ctxt × Ty)

  Γ : Ctxt
  τ : Ty

-- The expanded version os IsSatIx, IsTermIx and BoundarySat

IsSatIx : ∀ {ℐ : AnnIntr {𝒜} 𝒯} {ϑ : MetaVar (ATAnn 𝒜) Ψ Δ} {ix} →
  (eᵗ : ATAnn 𝒜 ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ) →
  ℐ ⊨[ ix ] esubstᵗ eᵗ ϑ →
  MetaVarIx ℐ ϑ → Set
IsSatIx {ix = ix} (# y) esat mvix =
  ix ≡ varIxᵗ mvix y
IsSatIx (proxy/t a e emᵗ) (proxy/i em ix ix′ ix◁ix′ psat esat) mvix =
  (ix ≡ annCtxtIxᵗ mvix a ×
   ix′ ≡ annIxᵗ mvix a) ×
  IsSatIx e esat mvix
IsSatIx (B# a ⟪ e ⟫) (B/i ix ix′ ix◁ix′ bsat esat) mvix =
  (ix ≡ annCtxtIxᵗ mvix a ×
   ix′ ≡ annIxᵗ mvix a) ×
  IsSatIx e esat mvix
IsSatIx ⋆ esat ⊨mv = ⊤
IsSatIx `z esat ⊨mv = ⊤
IsSatIx (`s e) (`s esat) ⊨mv = IsSatIx e esat ⊨mv
IsSatIx (foldN e ez es) (foldN esat ezsat essat) ⊨mv =
  IsSatIx e esat ⊨mv ×
  IsSatIx ez ezsat ⊨mv ×
  IsSatIx es essat ⊨mv
IsSatIx (assert e) (assert esat) ⊨mv = IsSatIx e esat ⊨mv
IsSatIx (e₁ `, e₂) (esat₁ `, esat₂) ⊨mv =
  IsSatIx e₁ esat₁ ⊨mv ×
  IsSatIx e₂ esat₂ ⊨mv
IsSatIx (π₁ e) (π₁ esat) ⊨mv = IsSatIx e esat ⊨mv
IsSatIx (π₂ e) (π₂ esat) ⊨mv = IsSatIx e esat ⊨mv
IsSatIx (inl e) (inl esat) ⊨mv = IsSatIx e esat ⊨mv
IsSatIx (inr e) (inr esat) ⊨mv = IsSatIx e esat ⊨mv
IsSatIx (case e of e₁ ∣ e₂) (case esat of esat₁ ∣ esat₂) ⊨mv =
  IsSatIx e esat ⊨mv ×
  IsSatIx e₁ esat₁ ⊨mv ×
  IsSatIx e₂ esat₂ ⊨mv
IsSatIx (box e) (box esat) ⊨mv = IsSatIx e esat ⊨mv
IsSatIx (unbox e) (unbox esat) ⊨mv = IsSatIx e esat ⊨mv
IsSatIx (` y) esat ⊨mv = ⊤
IsSatIx (ƛ e) (ƛ esat) ⊨mv = IsSatIx e esat ⊨mv
IsSatIx (e · eₐ) (esat · esatₐ) ⊨mv =
  IsSatIx e esat ⊨mv ×
  IsSatIx eₐ esatₐ ⊨mv
IsSatIx (unroll e) (unroll esat) ⊨mv = IsSatIx e esat ⊨mv
IsSatIx (roll τ e) (roll .τ esat) ⊨mv = IsSatIx e esat ⊨mv
IsSatIx (fix e) (fix esat) ⊨mv = IsSatIx e esat ⊨mv
IsSatIx (e ⨟ e₁) (esat ⨟ esat₁) ⊨mv =
  IsSatIx e esat ⊨mv ×
  IsSatIx e₁ esat₁ ⊨mv


BoundarySat : {ℐ : AnnIntr {𝒜} 𝒯} →
  (eᵗ : ATAnn 𝒜 ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ) →
  ∀ {ϑ : MetaVar (ATAnn 𝒜) Ψ Δ} → MetaVarIx ℐ ϑ → Set
BoundarySat (# y) mvix = ⊤
BoundarySat {ℐ = ℐ} (proxy/t a e emᵗ) {ϑ} mvix =
  (Σ[ ix◁ix′ ∈ (ℐ , annEnvᵗ ϑ a ⊢ annCtxtIxᵗ mvix a ◁ annIxᵗ mvix a) ]
    ℙ ℐ ⟦ _ , annEnvᵗ ϑ a , ix◁ix′ , monctorsubstᵗ emᵗ ϑ ⟧) ×
  BoundarySat e mvix
BoundarySat {ℐ = ℐ} (B# a ⟪ e ⟫) {ϑ} mvix =
  (Σ[ ix◁ix′ ∈ (ℐ , annEnvᵗ ϑ a ⊢ annCtxtIxᵗ mvix a ◁ annIxᵗ mvix a) ]
    𝔹 ℐ ⟦ _ , annEnvᵗ ϑ a , ix◁ix′ , esubstᵗ e ϑ ⟧) ×
  BoundarySat e mvix
BoundarySat ⋆ mvix = ⊤
BoundarySat `z mvix = ⊤
BoundarySat (`s e) mvix = BoundarySat e mvix
BoundarySat (foldN e ez es) mvix =
  BoundarySat e mvix ×
  BoundarySat ez mvix ×
  BoundarySat es mvix
BoundarySat (assert e) mvix = BoundarySat e mvix
BoundarySat (e₁ `, e₂) mvix =
  BoundarySat e₁ mvix ×
  BoundarySat e₂ mvix
BoundarySat (π₁ e) mvix = BoundarySat e mvix
BoundarySat (π₂ e) mvix = BoundarySat e mvix
BoundarySat (inl e) mvix = BoundarySat e mvix
BoundarySat (inr e) mvix = BoundarySat e mvix
BoundarySat (case e of e₁ ∣ e₂) mvix =
  BoundarySat e mvix ×
  BoundarySat e₁ mvix ×
  BoundarySat e₂ mvix
BoundarySat (box e) mvix = BoundarySat e mvix
BoundarySat (unbox e) mvix = BoundarySat e mvix
BoundarySat (` y) mvix = ⊤
BoundarySat (ƛ e) mvix = BoundarySat e mvix
BoundarySat (e · eₐ) mvix =
  BoundarySat e mvix ×
  BoundarySat eₐ mvix
BoundarySat (unroll e) mvix = BoundarySat e mvix
BoundarySat (roll τ e) mvix = BoundarySat e mvix
BoundarySat (fix e) mvix = BoundarySat e mvix
BoundarySat (e ⨟ e₁) mvix =
  BoundarySat e mvix ×
  BoundarySat e₁ mvix


IsTermIx : {ℐ : AnnIntr {𝒜} 𝒯} →
  (eᵗ : ATAnn 𝒜 ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ) →
  {ϑ : MetaVar (ATAnn 𝒜) Ψ Δ} → MetaVarIx ℐ ϑ → AIIx ℐ → Set
IsTermIx {𝒜 = 𝒜} {ℐ = ℐ} (# y) {ϑ = ϑ} mvix ix =
  (ℐ ⊨[ varIxᵗ mvix y ] termEnvᵗ ϑ y) → (ℐ ⊨[ ix ] termEnvᵗ ϑ y)
IsTermIx (proxy/t a e emᵗ) mvix ix =
  ix ≡ annCtxtIxᵗ mvix a ×
  IsTermIx e mvix (annIxᵗ mvix a)
IsTermIx (B# a ⟪ e ⟫) mvix ix =
  ix ≡ annCtxtIxᵗ mvix a ×
  IsTermIx e mvix (annIxᵗ mvix a)
IsTermIx ⋆ mvix ix = ⊤
IsTermIx `z mvix ix = ⊤
IsTermIx (`s e) mvix ix = IsTermIx e mvix ix
IsTermIx (foldN e ez es) mvix ix =
  IsTermIx e mvix ix ×
  IsTermIx ez mvix ix ×
  IsTermIx es mvix ix
IsTermIx (assert e) mvix ix = IsTermIx e mvix ix
IsTermIx (e₁ `, e₂) mvix ix = IsTermIx e₁ mvix ix × IsTermIx e₂ mvix ix
IsTermIx (π₁ e) mvix ix = IsTermIx e mvix ix
IsTermIx (π₂ e) mvix ix = IsTermIx e mvix ix
IsTermIx (inl e) mvix ix = IsTermIx e mvix ix
IsTermIx (inr e) mvix ix = IsTermIx e mvix ix
IsTermIx (case e of e₁ ∣ e₂) mvix ix =
  IsTermIx e mvix ix ×
  IsTermIx e₁ mvix ix ×
  IsTermIx e₂ mvix ix
IsTermIx (box e) mvix ix = IsTermIx e mvix ix
IsTermIx (unbox e) mvix ix = IsTermIx e mvix ix
IsTermIx (` y) mvix ix = ⊤
IsTermIx (ƛ e) mvix ix = IsTermIx e mvix ix
IsTermIx (e · eₐ) mvix ix = IsTermIx e mvix ix × IsTermIx eₐ mvix ix
IsTermIx (unroll e) mvix ix = IsTermIx e mvix ix
IsTermIx (roll τ e) mvix ix = IsTermIx e mvix ix
IsTermIx (fix e) mvix ix = IsTermIx e mvix ix
IsTermIx (e ⨟ e₁) mvix ix = IsTermIx e mvix ix × IsTermIx e₁ mvix ix
