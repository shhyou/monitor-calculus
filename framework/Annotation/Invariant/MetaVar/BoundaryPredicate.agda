{-# OPTIONS --without-K --safe #-}

module Annotation.Invariant.MetaVar.BoundaryPredicate where

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import Annotation.Language
open import Annotation.Invariant.Base
open import Annotation.Invariant.MetaVar.Base
open import Annotation.Invariant.MetaVar.Predicate

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe; maybe′)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

private variable
  𝒜 : AnnTerm
  𝒯 : AnnTransit 𝒜

  Ψ : List Ty
  Δ : List (Ctxt × Ty)

  Γ : Ctxt
  τ : Ty


IsSatIxPred : {ℐ : AnnInvr {𝒜} 𝒯} →
  TermTmplPred ℐ
IsSatIxPred {ℐ = ℐ} = record
  { P = λ ϑ eᵗ →
      ∃ λ ix →
        ℐ ⊨[ ix ] esubstᵗ eᵗ ϑ
  ; varPred? = just (λ _ _ _ _ y → λ ix,esat mvix ix* →
      let ix = proj₁ ix,esat; esat = proj₂ ix,esat in
      (ix ≡ varIxᵗ mvix y))
  ; proxyPred = λ a eᵗ emᵗ → λ where
      (_ , proxy/i em ix ix′ ix◁ix′ psat esat) mvix ix* →
        (ix ≡ annCtxtIxᵗ mvix a) × (ix′ ≡ annIxᵗ mvix a)
  ; boundaryPred = λ a eᵗ → λ where
      (_ , B/i ix ix′ ix◁ix′ bsat esat) mvix ix* →
        (ix ≡ annCtxtIxᵗ mvix a) × (ix′ ≡ annIxᵗ mvix a)
  ; isSatDownwardClosed = λ ϑ → record
      { proxy↓ = λ where (.ix , proxy/i em ix ix′ ix◁ix′ psat esat) → ix′ , esat
      ; B↓ = λ where (.ix , B/i ix ix′ ix◁ix′ bsat esat) → ix′ , esat
      ; `s↓ = λ where (ix , `s esat) → ix , esat
      ; foldN↓ = λ where
          (ix , foldN esat esatz esats) →
            (ix , esat) ,′
            (ix , esatz) ,′
            (ix , esats)
      ; assert↓ = λ where (ix , assert esat) → ix , esat
      ; cons↓ = λ where
          (ix , (esat₁ `, esat₂)) →
            (ix , esat₁) ,′
            (ix , esat₂)
      ; π₁↓ = λ where (ix , π₁ esat) → ix , esat
      ; π₂↓ = λ where (ix , π₂ esat) → ix , esat
      ; inl↓ = λ where (ix , inl esat) → ix , esat
      ; inr↓ = λ where (ix , inr esat) → ix , esat
      ; case↓ = λ where
          (ix , case esat of esat₁ ∣ esat₂) →
            (ix , esat) ,′
            (ix , esat₁) ,′
            (ix , esat₂)
      ; box↓ = λ where (ix , box esat) → ix , esat
      ; unbox↓ = λ where (ix , unbox esat) → ix , esat
      ; ƛ↓ = λ where (ix , ƛ esat) → ix , esat
      ; app↓ = λ where
          (ix , esat · esatₐ) →
            (ix , esat) ,′
            (ix , esatₐ)
      ; unroll↓ = λ where (ix , unroll esat) → ix , esat
      ; roll↓ = λ where (ix , roll τ esat) → ix , esat
      ; fix↓ = λ where (ix , fix esat) → ix , esat
      ; seq↓ = λ where
          (ix , esat ⨟ esat₁) →
            (ix , esat) ,′
            (ix , esat₁)
      }
  }

IsSatIx : ∀ {ℐ : AnnInvr {𝒜} 𝒯} →
  (eᵗ : ATAnn 𝒜 ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ) →
  {ϑ : MetaVar (ATAnn 𝒜) Ψ Δ} →
  (∃ λ ix → ℐ ⊨[ ix ] esubstᵗ eᵗ ϑ) →
  MetaVarIx ℐ ϑ → AIIx ℐ → Set
IsSatIx =
  TermTmplPred⇒MetaVarIxPred IsSatIxPred


IsTermIxPred : {ℐ : AnnInvr {𝒜} 𝒯} → TermTmplPred ℐ
IsTermIxPred {𝒜 = 𝒜} {ℐ = ℐ} = record
  { P = λ ϑ eᵗ → ⊤
  ; varPred? = just (λ _ _ _ _ y → λ {ϑ = ϑ} tt:⊤ mvix ix* →
      let ⊨y = termEnvᵗ ϑ y in
      ℐ ⊨[ varIxᵗ mvix y ] ⊨y →
      ℐ ⊨[ ix* ] ⊨y)
  ; proxyPred = λ a eᵗ emᵗ → λ tt:⊤ mvix ix* →
      (ix* ≡ annCtxtIxᵗ mvix a)
  ; boundaryPred = λ a eᵗ → λ tt:⊤ mvix ix* →
      (ix* ≡ annCtxtIxᵗ mvix a)
  ; isSatDownwardClosed = λ ϑ → trivialIsSatDownwardClosed
  }

IsTermIx : {ℐ : AnnInvr {𝒜} 𝒯} →
  (eᵗ : ATAnn 𝒜 ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ) →
  {ϑ : MetaVar (ATAnn 𝒜) Ψ Δ} →
  ⊤ → MetaVarIx ℐ ϑ → AIIx ℐ → Set
IsTermIx = TermTmplPred⇒MetaVarIxPred IsTermIxPred


BoundarySatPred : {ℐ : AnnInvr {𝒜} 𝒯} → TermTmplPred ℐ
BoundarySatPred {ℐ = ℐ} = record
  { P = λ ϑ eᵗ → ⊤
  ; varPred? = nothing
  ; proxyPred = λ a e emᵗ → λ {ϑ = ϑ} tt:⊤ mvix ix* →
      let A = annEnvᵗ ϑ a
          ix = annCtxtIxᵗ mvix a
          ix′ = annIxᵗ mvix a in
      Σ (ℐ , A ⊢ ix ◁ ix′) (λ ix◁ix′ →
        ℙ ℐ ⟦ _ , A , ix◁ix′ , monctorsubstᵗ emᵗ ϑ ⟧)
  ; boundaryPred = λ a e → λ {ϑ = ϑ} tt:⊤ mvix ix* →
      let A = annEnvᵗ ϑ a
          ix = annCtxtIxᵗ mvix a
          ix′ = annIxᵗ mvix a in
      Σ (ℐ , A ⊢ ix ◁ ix′) (λ ix◁ix′ →
        𝔹 ℐ ⟦ _ , A , ix◁ix′ , esubstᵗ e ϑ ⟧)
  ; isSatDownwardClosed = λ ϑ → trivialIsSatDownwardClosed
  }

BoundarySat : {ℐ : AnnInvr {𝒜} 𝒯} →
  (eᵗ : ATAnn 𝒜 ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ) →
  {ϑ : MetaVar (ATAnn 𝒜) Ψ Δ} →
  ⊤ → MetaVarIx ℐ ϑ → AIIx ℐ → Set
BoundarySat = TermTmplPred⇒MetaVarIxPred BoundarySatPred
