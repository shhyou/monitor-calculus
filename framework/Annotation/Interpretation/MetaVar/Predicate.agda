{-# OPTIONS --without-K --safe #-}

module Annotation.Interpretation.MetaVar.Predicate where

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import Annotation.Language
open import Annotation.Interpretation.Base
open import Annotation.Interpretation.MetaVar.Base

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe; maybe′)
import Data.Maybe.Properties as Maybe

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (_∋_; id)

private variable
  𝒜 : AnnTerm
  𝒯 : AnnTransit 𝒜

  Ψ : List Ty
  Δ : List (Ctxt × Ty)

  Γ : Ctxt
  τ : Ty

record TermTmplPred (ℐ : AnnIntr {𝒜} 𝒯)
  : Set₁ where
  inductive; no-eta-equality
  open AnnTerm 𝒜

  field
    P : MetaVar Ann Ψ Δ → (Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ) → Set
    isSatDownwardClosed : ∀ {Ψ Δ} (ϑ : MetaVar Ann Ψ Δ) → IsSatDownwardClosed (P ϑ)

  MetaVarIxPred : ∀ Ψ Δ → (eᵗ : Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ) → Set₁
  MetaVarIxPred Ψ Δ eᵗ =
    {ϑ : MetaVar Ann Ψ Δ} →
    P ϑ eᵗ →
    MetaVarIx ℐ ϑ →
    AIIx ℐ →
    Set

  field
    varPred? :
      Maybe (∀ Ψ Δ Γ τ →
            (y : (Γ ,′ τ) ∈ Δ) →
            -----------------------
            MetaVarIxPred Ψ Δ (# y))

    proxyPred :
      (a : τ ∈ Ψ) →
      ∀ eᵗ →
      (emᵗ : Ann ⨟ Ψ ⨟ Δ ∣ eᵗ ismonctorofᵗ τ) →
      -------------------------------------------------------
      MetaVarIxPred Ψ Δ (Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ  ∋  proxy/t a eᵗ emᵗ)

    boundaryPred :
      (a : τ ∈ Ψ) →
      (eᵗ : Ann ⨟ Ψ ⨟ Δ ∣ [] ⊢ τ) →
      --------------------------------------------------
      MetaVarIxPred Ψ Δ (Ann ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ  ∋  B# a ⟪ eᵗ ⟫)

varPred! : ∀ {ℐ : AnnIntr {𝒜} 𝒯} {Ψ Δ Γ τ} →
  (tmplPred : TermTmplPred ℐ) →
  (y : (Γ ,′ τ) ∈ Δ) →
  TermTmplPred.MetaVarIxPred tmplPred Ψ Δ (# y)
varPred! {Ψ = Ψ} {Δ} {Γ} {τ} tmplPred =
  (maybe′ id
          (λ Ψ Δ Γ τ eᵗ {ϑ} p mvix ix* → ⊤)
          (TermTmplPred.varPred? tmplPred))
  Ψ Δ Γ τ

varPred!-just : ∀ {ℐ : AnnIntr {𝒜} 𝒯} {Ψ Δ Γ τ} →
  (tmplPred : TermTmplPred ℐ) →
  {varPred : ∀ Ψ Δ Γ τ →
    (y : (Γ ,′ τ) ∈ Δ) →
    TermTmplPred.MetaVarIxPred tmplPred Ψ Δ (# y)} →
  TermTmplPred.varPred? tmplPred ≡ just varPred →
  varPred! tmplPred ≡ varPred Ψ Δ Γ τ
varPred!-just {Ψ = Ψ} {Δ} {Γ} {τ} tmplPred varPred?≡just
  with TermTmplPred.varPred? tmplPred
... | just varPred′ =
  Maybe.just-injective (cong (Maybe.map λ varPred″ → varPred″ Ψ Δ Γ τ)
                             varPred?≡just)

varPred!-nothing : ∀ {ℐ : AnnIntr {𝒜} 𝒯} {Ψ Δ Γ τ} →
  (tmplPred : TermTmplPred ℐ) →
  TermTmplPred.varPred? tmplPred ≡ nothing →
  varPred! {Ψ = Ψ} {Δ} {Γ} {τ} tmplPred ≡ λ eᵗ {ϑ} p mvix ix* → ⊤
varPred!-nothing tmplPred varPred?≡nothing
  with TermTmplPred.varPred? tmplPred
... | nothing = refl

TermTmplPred⇒MetaVarIxPred : {ℐ : AnnIntr {𝒜} 𝒯} →
  (tmplPred : TermTmplPred ℐ) →
  (eᵗ : ATAnn 𝒜 ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ) →
  {ϑ : MetaVar (ATAnn 𝒜) Ψ Δ} →
  TermTmplPred.P tmplPred ϑ eᵗ →
  MetaVarIx ℐ ϑ →
  AIIx ℐ →
  Set
TermTmplPred⇒MetaVarIxPred tmplPred (# y) {ϑ} p mvix ix* =
  varPred! tmplPred y p mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (proxy/t a e emᵗ) {ϑ} p mvix ix* =
  TermTmplPred.proxyPred tmplPred a e emᵗ p mvix ix* ×
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.proxy↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix (annIxᵗ mvix a)
TermTmplPred⇒MetaVarIxPred tmplPred (B# a ⟪ e ⟫) {ϑ} p mvix ix* =
  TermTmplPred.boundaryPred tmplPred a e p mvix ix* ×
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.B↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix (annIxᵗ mvix a)
TermTmplPred⇒MetaVarIxPred tmplPred ⋆ p mvix ix* = ⊤
TermTmplPred⇒MetaVarIxPred tmplPred `z p mvix ix* = ⊤
TermTmplPred⇒MetaVarIxPred tmplPred (`s e) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.`s↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (foldN e ez es) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred tmplPred e (proj₁ p,pz,ps) mvix ix* ×
  TermTmplPred⇒MetaVarIxPred tmplPred ez (proj₁ (proj₂ p,pz,ps)) mvix ix* ×
  TermTmplPred⇒MetaVarIxPred tmplPred es (proj₂ (proj₂ p,pz,ps)) mvix ix*
  where p,pz,ps = IsSatDownwardClosed.foldN↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p
TermTmplPred⇒MetaVarIxPred tmplPred (assert e) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.assert↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (e₁ `, e₂) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred tmplPred e₁ (proj₁ p₁,p₂) mvix ix* ×
  TermTmplPred⇒MetaVarIxPred tmplPred e₂ (proj₂ p₁,p₂) mvix ix*
  where p₁,p₂ = IsSatDownwardClosed.cons↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p
TermTmplPred⇒MetaVarIxPred tmplPred (π₁ e) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.π₁↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (π₂ e) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.π₂↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (inl e) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.inl↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (inr e) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.inr↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (case e of e₁ ∣ e₂) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred tmplPred e (proj₁ p,p₁,p₂) mvix ix* ×
  TermTmplPred⇒MetaVarIxPred tmplPred e₁ (proj₁ (proj₂ p,p₁,p₂)) mvix ix* ×
  TermTmplPred⇒MetaVarIxPred tmplPred e₂ (proj₂ (proj₂ p,p₁,p₂)) mvix ix*
  where p,p₁,p₂ = IsSatDownwardClosed.case↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p
TermTmplPred⇒MetaVarIxPred tmplPred (box e) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.box↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (unbox e) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.unbox↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (` y) p mvix ix* = ⊤
TermTmplPred⇒MetaVarIxPred tmplPred (ƛ e) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.ƛ↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (e · eₐ) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred tmplPred e (proj₁ p,pₐ) mvix ix* ×
  TermTmplPred⇒MetaVarIxPred tmplPred eₐ (proj₂ p,pₐ) mvix ix*
  where p,pₐ = IsSatDownwardClosed.app↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p
TermTmplPred⇒MetaVarIxPred tmplPred (unroll e) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.unroll↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (roll τ e) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.roll↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (fix e) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred
    tmplPred e
    (IsSatDownwardClosed.fix↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p)
    mvix ix*
TermTmplPred⇒MetaVarIxPred tmplPred (e ⨟ e₁) {ϑ} p mvix ix* =
  TermTmplPred⇒MetaVarIxPred tmplPred e (proj₁ p,p₁) mvix ix* ×
  TermTmplPred⇒MetaVarIxPred tmplPred e₁ (proj₂ p,p₁) mvix ix*
  where p,p₁ = IsSatDownwardClosed.seq↓ (TermTmplPred.isSatDownwardClosed tmplPred ϑ) p
