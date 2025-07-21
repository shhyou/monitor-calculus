{-# OPTIONS --without-K --no-infer-absurd-clauses --safe #-}

module Annotation.Interpretation.Property where

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import Annotation.Language
open import Annotation.Interpretation.Base
open import Annotation.Interpretation.MetaVar
open import Annotation.Interpretation.Decompose

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

record TermSat (ℐ : AnnIntr {𝒜} 𝒯)
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

InterpProperty : {𝒜 : AnnTerm} → Set₂
InterpProperty {𝒜} =
  ∀ {𝒯} →
  (ℐ : AnnIntr {𝒜} 𝒯) →
  (tag : RuleTag) →
  ∀ {τ} ix s₁ s₂ (e₁ e₂ : ATAnn 𝒜 ∣ [] ⊢ τ) →
    (step  : ATStep 𝒜 (AnnRules (ATAnn 𝒜) tag , 𝒯 tag) s₁ e₁ s₂ e₂) →
    (esat₁ : ℐ ⊨[ ix ] Term.substedExpr (ATStep.term₁ step)) →
    Set₁

TransitInterpIs : AnnIntr {𝒜} 𝒯 → InterpProperty → RuleTag → Set₁
TransitInterpIs {𝒜} {𝒯} ℐ Property tag =
  ∀ {τ ix s₁ s₂} {e₁ e₂ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    (step  : ATStep 𝒜 (AnnRules (ATAnn 𝒜) tag , 𝒯 tag) s₁ e₁ s₂ e₂) →
    (esat₁ : ℐ ⊨[ ix ] Term.substedExpr (ATStep.term₁ step)) →
    Property ℐ tag ix s₁ s₂ e₁ e₂ step esat₁

AnnTransitInterpIs : (ℐ : AnnIntr {𝒜} 𝒯) → InterpProperty → Set₁
AnnTransitInterpIs {𝒜 = 𝒜} {𝒯 = 𝒯} ℐ Property =
  (tag : RuleTag) → TransitInterpIs ℐ Property tag

Monotonic : ∀ {𝒜} → InterpProperty {𝒜}
Monotonic {𝒜} ℐ tag ix s₁ s₂ e₁ e₂ step esat₁ =
  (assumption : TermSat ℐ (proj₁ ∘ AnnRulesMVIxPredView 𝒜 tag (ATStep.tyvars step))
                           (ATStep.term₁ step)
                           esat₁) →
  ∃[ I₂ ] ℐ ⊢ (s₁ , TermSat.inv assumption) ≼ (s₂ , I₂)

record SoundSat (ℐ : AnnIntr {𝒜} 𝒯)
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

Sound : ∀ {𝒜} → InterpProperty {𝒜}
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
