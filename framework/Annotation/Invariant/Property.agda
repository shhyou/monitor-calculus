{-# OPTIONS --without-K --no-infer-absurd-clauses --safe #-}

module Annotation.Invariant.Property where

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import Annotation.Language
open import Annotation.Invariant.Base
open import Annotation.Invariant.MetaVar
open import Annotation.Invariant.Decompose

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base using (List; []; _∷_; length; lookup)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (_∘_)

private variable
  𝒜 : AnnTerm
  𝒯 : AnnTransit 𝒜

  Ψ : List Ty
  Δ : List (Ctxt × Ty)

  Γ : Ctxt
  τ : Ty

record TermSat (ℐ : AnnInvr {𝒜} 𝒯)
  {s} {e : ATAnn 𝒜 ∣ [] ⊢ τ}
  {termtmpl : TermTmpl (ATAnn 𝒜) Δ τ}
  (mkPredView : (tmplPred : TermTmplPred ℐ) → MVIxPredView (exprᵗ termtmpl) tmplPred)
  {termEnv : MEnv (ATAnn 𝒜) Δ}
  (term : Term (ATAnn 𝒜) termtmpl termEnv e)
  {ix : AIIx ℐ}
  (esat : ℐ ⊨[ ix ] esubstᵗ (exprᵗ termtmpl) (Term.metaVars term))
  : Set₁ where
    inductive
    constructor mkTermSat
    field
      metaVarIx : MetaVarIx ℐ (Term.metaVars term)
      isSatIx : MVIxPredView.Pred (mkPredView IsSatIxPred) (ix , esat) metaVarIx ix

      inv : AIInv ℐ s
      metaVarSat : MetaVarSat ℐ termEnv (varIxᵗ metaVarIx)
      boundarySat : MVIxPredView.Pred (mkPredView BoundarySatPred) tt metaVarIx ix

InvrProperty : {𝒜 : AnnTerm} → Set₂
InvrProperty {𝒜} =
  ∀ {𝒯} →
  (ℐ : AnnInvr {𝒜} 𝒯) →
  (tag : RuleTag) →
  ∀ {τ} ix s₁ s₂ (e₁ e₂ : ATAnn 𝒜 ∣ [] ⊢ τ) →
    (step  : ATStep 𝒜 (AnnRules (ATAnn 𝒜) tag , 𝒯 tag) s₁ e₁ s₂ e₂) →
    (esat₁ : ℐ ⊨[ ix ] Term.substedExpr (ATStep.term₁ step)) →
    Set₁

InvrForRuleIs : AnnInvr {𝒜} 𝒯 → InvrProperty → RuleTag → Set₁
InvrForRuleIs {𝒜} {𝒯} ℐ Property tag =
  ∀ {τ ix s₁ s₂} {e₁ e₂ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    (step  : ATStep 𝒜 (AnnRules (ATAnn 𝒜) tag , 𝒯 tag) s₁ e₁ s₂ e₂) →
    (esat₁ : ℐ ⊨[ ix ] Term.substedExpr (ATStep.term₁ step)) →
    Property ℐ tag ix s₁ s₂ e₁ e₂ step esat₁

AnnInvrIs : (ℐ : AnnInvr {𝒜} 𝒯) → InvrProperty → Set₁
AnnInvrIs {𝒜 = 𝒜} {𝒯 = 𝒯} ℐ Property =
  (tag : RuleTag) → InvrForRuleIs ℐ Property tag

Monotonic : ∀ {𝒜} → InvrProperty {𝒜}
Monotonic {𝒜} ℐ tag ix s₁ s₂ e₁ e₂ step esat₁ =
  (assumption : TermSat ℐ (proj₁ ∘ AnnRulesMVIxPredView 𝒜 tag (ATStep.tyvars step))
                           (ATStep.term₁ step)
                           esat₁) →
  ∃[ I₂ ] ℐ ⊢ (s₁ , TermSat.inv assumption) ≼ (s₂ , I₂)

record SoundSat (ℐ : AnnInvr {𝒜} 𝒯)
  (termtmpl : TermTmpl (ATAnn 𝒜) Δ τ)
  (mkPredView : (tmplPred : TermTmplPred ℐ) → MVIxPredView (exprᵗ termtmpl) tmplPred)
  (ϑ : MetaVar (ATAnn 𝒜) (annCtxt termtmpl) Δ)
  (varix : VarIx ℐ Δ)
  (ix : AIIx ℐ)
  : Set where
    inductive; no-eta-equality
    field
      annCtxtIx : AnnIx ℐ (annCtxt termtmpl)
      annIx : AnnIx ℐ (annCtxt termtmpl)

    metaVarIx : MetaVarIx ℐ ϑ
    metaVarIx = mkMVIx varix annCtxtIx annIx

    field
      isTermIx : MVIxPredView.Pred (mkPredView IsTermIxPred) tt metaVarIx ix
      boundarySat : MVIxPredView.Pred (mkPredView BoundarySatPred) tt metaVarIx ix

Sound : ∀ {𝒜} → InvrProperty {𝒜}
Sound {𝒜 = 𝒜} ℐ tag ix s₁ s₂ e₁ e₂ step esat₁ =
  (assumption : TermSat ℐ (proj₁ ∘ AnnRulesMVIxPredView 𝒜 tag (ATStep.tyvars step))
                          (ATStep.term₁ step)
                          esat₁) →
  ∃[ I₂ ] ℐ ⊢ (s₁ , TermSat.inv assumption) ≼ (s₂ , I₂) →
  let mvix₁ = TermSat.metaVarIx assumption in
  SoundSat ℐ (ATStep.termTmpl₂ step)
              (proj₂ ∘ AnnRulesMVIxPredView 𝒜 tag (ATStep.tyvars step))
              (Term.metaVars (ATStep.term₂ step))
              (varIxᵗ mvix₁)
              ix
