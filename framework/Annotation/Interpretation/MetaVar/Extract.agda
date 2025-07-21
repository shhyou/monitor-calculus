{-# OPTIONS --without-K --safe #-}

module Annotation.Interpretation.MetaVar.Extract where

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import Annotation.Language
open import Annotation.Interpretation.Base
open import Annotation.Interpretation.MetaVar.Base
open import Annotation.Interpretation.MetaVar.BoundaryPredicate

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst; cong; sym; trans)

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
  τ : Ty

MetaVarExtractible : (𝒜 : AnnTerm) → Rule (ATAnn 𝒜) → Set₁
MetaVarExtractible 𝒜 R =
  let open Rule R in
  (tyvars : TyVars) →
  let e₁ = exprᵗ (prTermTmpl₁ (mkPreRule tyvars)) in
  ∀ {𝒯} {ℐ : AnnIntr {𝒜} 𝒯} {ix₀ ϑ} →
    (esat₁ : (ℐ ⊨[ ix₀ ] esubstᵗ e₁ ϑ)) →
    Σ[ mvix ∈  MetaVarIx ℐ ϑ ]
      IsSatIx e₁ (ix₀ , esat₁) mvix ix₀ ×
      MetaVarSat ℐ (termEnvᵗ ϑ) (varIxᵗ mvix)

AnnRulesExtractMetaVar :  (𝒜 : AnnTerm) →
                          (tag : RuleTag) →
                          MetaVarExtractible 𝒜 (AnnRules (ATAnn 𝒜) tag)
AnnRulesExtractMetaVar 𝒜 `R-cross-unit
    (τ , refl) (B/i ix ix′ ix◁ix′ bsat ℐ,s⊨e) =
      mkMVIx (λ ())
             (λ where (here refl) → ix)
             (λ where (here refl) → ix′) ,
      ((refl ,′ refl) ,′ tt) ,′
      (λ ())
AnnRulesExtractMetaVar 𝒜 `R-cross-nat
    (τ , refl) (B/i ix ix′ ix◁ix′ bsat ℐ,s⊨e) =
      mkMVIx (λ where (here refl) → ix′)
             (λ where (here refl) → ix)
             (λ where (here refl) → ix′) ,
      ((refl ,′ refl) ,′ refl) ,′
      (λ where (here refl) → ℐ,s⊨e)
AnnRulesExtractMetaVar 𝒜 `R-cross-cons
    (τ , (τ₁ , τ₂) , refl) (B/i ix ix′ ix◁ix′ bsat (ℐ,s⊨e₁ `, ℐ,s⊨e₂)) =
      mkMVIx (λ where
               (here refl) → ix′
               (there (here refl)) → ix′)
             (λ where (here refl) → ix)
             (λ where (here refl) → ix′) ,
      ((refl ,′ refl) ,′ refl ,′ refl) ,′
      (λ where
        (here refl) → ℐ,s⊨e₁
        (there (here refl)) → ℐ,s⊨e₂)
AnnRulesExtractMetaVar 𝒜 `R-cross-inl
    (τ , (τ₁ , τ₂) , refl) (B/i ix ix′ ix◁ix′ bsat (inl ℐ,s⊨e)) =
      mkMVIx (λ where (here refl) → ix′)
             (λ where (here refl) → ix)
             (λ where (here refl) → ix′) ,
      ((refl ,′ refl) ,′ refl) ,′
      (λ where (here refl) → ℐ,s⊨e)
AnnRulesExtractMetaVar 𝒜 `R-cross-inr
    (τ , (τ₁ , τ₂) , refl) (B/i ix ix′ ix◁ix′ bsat (inr ℐ,s⊨e)) =
      mkMVIx (λ where (here refl) → ix′)
             (λ where (here refl) → ix)
             (λ where (here refl) → ix′) ,
      ((refl ,′ refl) ,′ refl) ,′
      (λ where (here refl) → ℐ,s⊨e)
AnnRulesExtractMetaVar 𝒜 `R-cross-roll
    (τ , τ′ , refl) (B/i ix ix′ ix◁ix′ bsat (roll .τ′ ℐ,s⊨e)) =
      mkMVIx (λ where (here refl) → ix′)
             (λ where (here refl) → ix)
             (λ where (here refl) → ix′) ,
      ((refl ,′ refl) ,′ refl) ,′
      (λ where (here refl) → ℐ,s⊨e)
AnnRulesExtractMetaVar 𝒜 `R-cross-box
    (τ , τ′ , refl) (B/i ix ix′ ix◁ix′ bsat (box ℐ,s⊨e)) =
      mkMVIx (λ where (here refl) → ix′)
             (λ where (here refl) → ix)
             (λ where (here refl) → ix′) ,
      ((refl ,′ refl) ,′ refl) ,′
      (λ where (here refl) → ℐ,s⊨e)
AnnRulesExtractMetaVar 𝒜 `R-cross-lam
    (τ , (τₐ , τᵣ) , refl) (B/i ix ix′ ix◁ix′ bsat (ƛ ℐ,s⊨e)) =
      mkMVIx (λ where (here refl) → ix′)
             (λ where (here refl) → ix)
             (λ where (here refl) → ix′) ,
      ((refl ,′ refl) ,′ refl) ,′
      (λ where (here refl) → ℐ,s⊨e)
AnnRulesExtractMetaVar 𝒜 `R-merge-box
    (τ , τ′ , refl) (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (box ℐ,s⊨e))) =
      mkMVIx (λ where (here refl) → ix″)
             (λ where
               (here refl) → ix
               (there (here refl)) → ix′)
             (λ where
               (here refl) → ix′
               (there (here refl)) → ix″) ,
      ((refl ,′ refl) ,′ (refl ,′ refl) ,′ refl) ,′
      (λ where (here refl) → ℐ,s⊨e)
AnnRulesExtractMetaVar 𝒜 `R-merge-lam
    (τ , (τₐ , τᵣ) , refl) (B/i ix ix′ ix◁ix′ bsat (proxy/i em .ix′ ix″ ix′◁ix″ psat (ƛ ℐ,s⊨e))) =
      mkMVIx (λ where (here refl) → ix″)
             (λ where
               (here refl) → ix
               (there (here refl)) → ix′)
             (λ where
               (here refl) → ix′
               (there (here refl)) → ix″) ,
      ((refl ,′ refl) ,′ (refl ,′ refl) ,′ refl) ,′
      (λ where (here refl) → ℐ,s⊨e)
AnnRulesExtractMetaVar 𝒜 `R-proxy-unbox
    (τ , tt) (unbox (proxy/i em ix ix′ ix◁ix′ psat (box ℐ,s⊨e))) =
      mkMVIx (λ where (here refl) → ix′)
             (λ where (here refl) → ix)
             (λ where (here refl) → ix′) ,
      ((refl ,′ refl) ,′ refl) ,′
      (λ where (here refl) → ℐ,s⊨e)
AnnRulesExtractMetaVar 𝒜 `R-proxy-β
    (τᵣ , τₐ) (proxy/i em ix ix′ ix◁ix′ psat (ƛ ℐ,s⊨e)  ·  ℐ,s⊨eₐ) =
      mkMVIx (λ where
               (here refl) → ix′
               (there (here refl)) → ix)
             (λ where (here refl) → ix)
             (λ where (here refl) → ix′) ,
      (((refl ,′ refl) ,′ refl) ,′ refl) ,′
      (λ where
        (here refl) → ℐ,s⊨e
        (there (here refl)) → ℐ,s⊨eₐ)
