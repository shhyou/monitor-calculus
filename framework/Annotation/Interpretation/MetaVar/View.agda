{-# OPTIONS --without-K --safe --no-infer-absurd-clauses #-}

module Annotation.Interpretation.MetaVar.View where

open import Utils.Misc
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import Annotation.Language
open import Annotation.Interpretation.Base
open import Annotation.Interpretation.MetaVar.Base
open import Annotation.Interpretation.MetaVar.Predicate

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst; cong; sym; trans)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe; maybe′)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (_∋_; id)
open import Function.Bundles using (Inverse; _↔_)
open import Function.Construct.Identity using (↔-id)
open import Function.Construct.Symmetry using (↔-sym)
open import Function.Construct.Composition using (_↔-∘_)

private variable
  𝒜 : AnnTerm
  𝒯 : AnnTransit 𝒜

  Ψ : List Ty
  Δ : List (Ctxt × Ty)

  Γ : Ctxt
  τ : Ty


record MVIxPredView {ℐ : AnnIntr {𝒜} 𝒯}
  (eᵗ : ATAnn 𝒜 ⨟ Ψ ⨟ Δ ∣ Γ ⊢ τ)
  (tmplPred : TermTmplPred ℐ)
  : Set₁ where
  inductive; no-eta-equality
  field
    Pred : {ϑ : MetaVar (ATAnn 𝒜) Ψ Δ} →
      TermTmplPred.P tmplPred ϑ eᵗ →
      MetaVarIx ℐ ϑ →
      AIIx ℐ →
      Set
    iso : ∀ {ϑ} p mvix ix* →
      TermTmplPred⇒MetaVarIxPred tmplPred eᵗ {ϑ} p mvix ix* ↔
      Pred {ϑ} p mvix ix*


MVIxPredHasView : (𝒜 : AnnTerm) → Rule (ATAnn 𝒜) → Set₁
MVIxPredHasView 𝒜 R =
  let open Rule R in
  (tyvars : TyVars) →
  let open PreRule (mkPreRule tyvars) in
  ∀ {𝒯} {ℐ : AnnIntr {𝒜} 𝒯} →
    (tmplPred : TermTmplPred ℐ) →
    MVIxPredView (exprᵗ termTmpl₁) tmplPred ×
    MVIxPredView (exprᵗ termTmpl₂) tmplPred


AnnRulesMVIxPredView :  (𝒜 : AnnTerm) →
                        (tag : RuleTag) →
                        MVIxPredHasView 𝒜 (AnnRules (ATAnn 𝒜) tag)
AnnRulesMVIxPredView 𝒜 `R-cross-unit (τ , refl) tmplPred =
  let View₁ = TermTmplPred.boundaryPred tmplPred (here refl) ⋆ in
  record
    { Pred = λ p mvix ix* → View₁ p mvix ix*
    ; iso = λ p mvix ix* → ↔-×-identityˡ (↔-id (View₁ p mvix ix*))
    } ,′
  record
    { Pred = λ p mvix ix* → ⊤
    ; iso = λ p mvix ix* → ↔-id ⊤
    }
AnnRulesMVIxPredView 𝒜 `R-cross-nat (τ , refl) tmplPred
  with TermTmplPred.varPred? tmplPred in varPred?-eq
... | nothing =
  let View₁ = TermTmplPred.boundaryPred tmplPred (here refl) (#(here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        subst (λ f →
                (View₁ p mvix ix* ×
                  f (here refl) (B↓ p) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₁ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₁ p mvix ix*)))
    } ,′
  record
    { Pred = λ p mvix ix* → ⊤
    ; iso = λ p mvix ix* →
        subst (λ f → f (here refl) p mvix ix* ↔ ⊤)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-id ⊤)
    }
... | just varPred =
  let View₁ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (#(here refl)) p mvix ix* ×
        f (here refl) (B↓ p) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ (varPred _ _ _ _) p mvix ix*
    ; iso = λ p mvix ix* →
        subst (λ f → View₁ f p mvix ix* ↔ View₁ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₁ (varPred _ _ _ _) p mvix ix*))
    } ,′
  let View₂ = varPred _ _ _ _ (here refl) in
  record
    { Pred = λ p mvix ix* → View₂ p mvix ix*
    ; iso = λ p mvix ix* →
        subst (λ f → f (here refl) p mvix ix* ↔ View₂ p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₂ p mvix ix*))
    }
AnnRulesMVIxPredView 𝒜 `R-cross-cons (τ , (τ₁ , τ₂) , refl) tmplPred
  with TermTmplPred.varPred? tmplPred in varPred?-eq
... | nothing =
  let View₁ = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred using (boundaryPred) in
        boundaryPred (here refl) (#(here refl) `, #(there(here refl))) p mvix ix* in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ {ϑ} p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open IsSatDownwardClosed (TermTmplPred.isSatDownwardClosed tmplPred ϑ)
            p₁,p₂ = cons↓ (B↓ p) in
        -- Can't fold two substs into one because f is not polymorphic in (y : (Γ ,′ τ) ∈ Δ).
        -- This is also due to how varPred!-nothing places the implicit arguments: they
        -- (Ψ, Δ, Γ, and τ) are instantiated immediately at the call site of varPred!-nothing.
        subst (λ f →
                (View₁ p mvix ix* ×
                  varPred! tmplPred (here refl) (proj₁ p₁,p₂)  mvix (annIxᵗ mvix (here refl)) ×
                  f (there(here refl)) (proj₂ p₁,p₂) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₁ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (subst (λ f →
                      (View₁ p mvix ix* ×
                        f (here refl) (proj₁ p₁,p₂) mvix (annIxᵗ mvix (here refl)) ×
                        ⊤)
                      ↔
                      View₁ p mvix ix*)
                    (sym (varPred!-nothing tmplPred varPred?-eq))
                    (↔-×-identityˡ (↔-×-identityˡ (↔-id (View₁ {ϑ} p mvix ix*)))
                     ↔-∘
                     (↔-sym ↔-×-assoc)))
    } ,′
  let View₂ = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (# here refl) (proj₁ (cons↓ p)) mvix ix* ×
        boundaryPred (there(here refl)) (#(there(here refl))) (proj₂ (cons↓ p)) mvix ix* in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ {ϑ} p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ)
            p₁ = proj₁ (cons↓ p)
            p₂ = proj₂ (cons↓ p)
            ix₁ = annIxᵗ mvix (here refl)
            ix₂ = annIxᵗ mvix (there(here refl)) in
        -- Similar to the other direction: can't fold two substs into one because f
        -- is not polymorphic in (y : (Γ ,′ τ) ∈ Δ).
        subst (λ f →
                ((boundaryPred (here refl) (# here refl) p₁ mvix ix* ×
                  varPred! tmplPred (here refl) (B↓ p₁) mvix ix₁) ×
                 (boundaryPred (there(here refl)) (#(there(here refl))) p₂ mvix ix* ×
                  f (there(here refl)) (B↓ p₂) mvix ix₂))
                ↔
                View₂ {ϑ} p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (subst (λ f →
                        ((boundaryPred (here refl) (# here refl) p₁ mvix ix* ×
                          f (here refl) (B↓ p₁) mvix ix₁) ×
                         (boundaryPred (there(here refl)) (#(there(here refl))) p₂ mvix ix* ×
                          ⊤))
                        ↔
                        View₂ {ϑ} p mvix ix*)
                      (sym (varPred!-nothing tmplPred varPred?-eq))
                      ((↔-×-identityˡ
                        (↔-id (boundaryPred (here refl) (# here refl) p₁ mvix ix*)))
                       ↔-,
                       (↔-×-identityˡ
                        (↔-id (boundaryPred (there(here refl)) (#(there(here refl)))
                                            p₂ mvix ix*)))))
    }
... | just varPred =
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ)
            p₁,p₂ = cons↓ (B↓ p)
            ix = annIxᵗ mvix (here refl) in
        boundaryPred (here refl) (#(here refl) `, #(there(here refl))) p mvix ix* ×
        varPred _ _ _ _ (here refl) (proj₁ p₁,p₂) mvix ix ×
        varPred _ _ _ _ (there(here refl)) (proj₂ p₁,p₂) mvix ix
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ)
            p₁,p₂ = cons↓ (B↓ p)
            ix = annIxᵗ mvix (here refl) in
        subst (λ f →
                (boundaryPred (here refl) (#(here refl) `, #(there(here refl))) p mvix ix* ×
                 f (here refl) (proj₁ p₁,p₂) mvix ix ×
                 varPred! tmplPred (there(here refl)) (proj₂ p₁,p₂) mvix ix)
                ↔
                (boundaryPred (here refl) (#(here refl) `, #(there(here refl))) p mvix ix* ×
                 varPred _ _ _ _ (here refl) (proj₁ p₁,p₂) mvix ix ×
                 varPred _ _ _ _ (there(here refl)) (proj₂ p₁,p₂) mvix ix))
              (sym (varPred!-just tmplPred varPred?-eq))
              (subst (λ f →
                       (boundaryPred (here refl) (#(here refl) `, #(there(here refl))) p mvix ix* ×
                        varPred _ _ _ _ (here refl) (proj₁ p₁,p₂) mvix ix ×
                        f (there(here refl)) (proj₂ p₁,p₂) mvix ix)
                       ↔
                       (boundaryPred (here refl) (#(here refl) `, #(there(here refl))) p mvix ix* ×
                        varPred _ _ _ _ (here refl) (proj₁ p₁,p₂) mvix ix ×
                        varPred _ _ _ _ (there(here refl)) (proj₂ p₁,p₂) mvix ix))
                    (sym (varPred!-just tmplPred varPred?-eq))
                    (↔-id _))
    } ,′
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ)
            p₁ = proj₁ (cons↓ p)
            p₂ = proj₂ (cons↓ p)
            ix₁ = annIxᵗ mvix (here refl)
            ix₂ = annIxᵗ mvix (there(here refl)) in
        boundaryPred (here refl) (#(here refl)) p₁ mvix ix* ×
        varPred _ _ _ _ (here refl) (B↓ p₁) mvix ix₁ ×
        boundaryPred (there(here refl)) (#(there(here refl))) p₂ mvix ix* ×
        varPred _ _ _ _ (there(here refl)) (B↓ p₂) mvix ix₂
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ)
            p₁ = proj₁ (cons↓ p)
            p₂ = proj₂ (cons↓ p)
            ix₁ = annIxᵗ mvix (here refl)
            ix₂ = annIxᵗ mvix (there(here refl)) in
        subst (λ f →
                (boundaryPred (here refl) (#(here refl)) p₁ mvix ix* ×
                 f (here refl) (B↓ p₁) mvix ix₁ ×
                 boundaryPred (there(here refl)) (#(there(here refl))) p₂ mvix ix* ×
                 varPred! tmplPred (there(here refl)) (B↓ p₂) mvix ix₂)
                ↔
                (boundaryPred (here refl) (#(here refl)) p₁ mvix ix* ×
                 varPred _ _ _ _ (here refl) (B↓ p₁) mvix ix₁ ×
                 boundaryPred (there(here refl)) (#(there(here refl))) p₂ mvix ix* ×
                 varPred _ _ _ _ (there(here refl)) (B↓ p₂) mvix ix₂))
              (sym (varPred!-just tmplPred varPred?-eq))
              (subst (λ f →
                       (boundaryPred (here refl) (#(here refl)) p₁ mvix ix* ×
                        varPred _ _ _ _ (here refl) (B↓ p₁) mvix ix₁ ×
                        boundaryPred (there(here refl)) (#(there(here refl))) p₂ mvix ix* ×
                        f (there(here refl)) (B↓ p₂) mvix ix₂)
                       ↔
                       (boundaryPred (here refl) (#(here refl)) p₁ mvix ix* ×
                        varPred _ _ _ _ (here refl) (B↓ p₁) mvix ix₁ ×
                        boundaryPred (there(here refl)) (#(there(here refl))) p₂ mvix ix* ×
                        varPred _ _ _ _ (there(here refl)) (B↓ p₂) mvix ix₂))
                     (sym (varPred!-just tmplPred varPred?-eq))
                     (↔-id _))
        ↔-∘
        ↔-×-assoc
    }
AnnRulesMVIxPredView 𝒜 `R-cross-inl (τ , (τ₁ , τ₂) , refl) tmplPred
  with TermTmplPred.varPred? tmplPred in varPred?-eq
... | nothing =
  let View₁ = TermTmplPred.boundaryPred tmplPred (here refl) (inl (#(here refl))) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open IsSatDownwardClosed (TermTmplPred.isSatDownwardClosed tmplPred ϑ) in
        subst (λ f →
                (View₁ p mvix ix* ×
                  f (here refl) (inl↓ (B↓ p)) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₁ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₁ p mvix ix*)))
    } ,′
  let View₂ = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (# here refl) (inl↓ p) mvix ix* in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open IsSatDownwardClosed (TermTmplPred.isSatDownwardClosed tmplPred ϑ) in
        subst (λ f →
                (View₂ p mvix ix* ×
                  f (here refl) (B↓ (inl↓ p)) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₂ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₂ p mvix ix*)))
    }
... | just varPred =
  let View₁ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (inl (# here refl)) p mvix ix* ×
        f (here refl) (inl↓ (B↓ p)) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ (varPred _ _ _ _) p mvix ix*
    ; iso = λ p mvix ix* →
        subst (λ f → View₁ f p mvix ix* ↔ View₁ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₁ (varPred _ _ _ _) p mvix ix*))
    } ,′
  let View₂ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (# here refl) (inl↓ p) mvix ix* ×
        f (here refl) (B↓ (inl↓ p)) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ (varPred _ _ _ _) p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        subst (λ f → View₂ f p mvix ix* ↔ View₂ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₂ (varPred _ _ _ _) p mvix ix*))
    }
AnnRulesMVIxPredView 𝒜 `R-cross-inr (τ , (τ₁ , τ₂) , refl) tmplPred
  with TermTmplPred.varPred? tmplPred in varPred?-eq
... | nothing =
  let View₁ = TermTmplPred.boundaryPred tmplPred (here refl) (inr (#(here refl))) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        subst (λ f →
                (View₁ p mvix ix* ×
                  f (here refl) (inr↓ (B↓ p)) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₁ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₁ p mvix ix*)))
    } ,′
  let View₂ = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (# here refl) (inr↓ p) mvix ix* in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open IsSatDownwardClosed (TermTmplPred.isSatDownwardClosed tmplPred ϑ) in
        subst (λ f →
                (View₂ p mvix ix* ×
                  f (here refl) (B↓ (inr↓ p)) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₂ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₂ p mvix ix*)))
    }
... | just varPred =
  let View₁ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (inr (# here refl)) p mvix ix* ×
        f (here refl) (inr↓ (B↓ p)) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ (varPred _ _ _ _) p mvix ix*
    ; iso = λ p mvix ix* →
        subst (λ f → View₁ f p mvix ix* ↔ View₁ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₁ (varPred _ _ _ _) p mvix ix*))
    } ,′
  let View₂ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (# here refl) (inr↓ p) mvix ix* ×
        f (here refl) (B↓ (inr↓ p)) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ (varPred _ _ _ _) p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        subst (λ f → View₂ f p mvix ix* ↔ View₂ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₂ (varPred _ _ _ _) p mvix ix*))
    }
AnnRulesMVIxPredView 𝒜 `R-cross-roll (τ , τ′ , refl) tmplPred
  with TermTmplPred.varPred? tmplPred in varPred?-eq
... | nothing =
  let View₁ = TermTmplPred.boundaryPred tmplPred (here refl) (roll τ′ (#(here refl))) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        subst (λ f →
                (View₁ p mvix ix* ×
                  f (here refl) (roll↓ (B↓ p)) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₁ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₁ p mvix ix*)))
    } ,′
  let View₂ = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (# here refl) (roll↓ p) mvix ix* in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open IsSatDownwardClosed (TermTmplPred.isSatDownwardClosed tmplPred ϑ) in
        subst (λ f →
                (View₂ p mvix ix* ×
                  f (here refl) (B↓ (roll↓ p)) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₂ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₂ p mvix ix*)))
    }
... | just varPred =
  let View₁ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (roll τ′ (# here refl)) p mvix ix* ×
        f (here refl) (roll↓ (B↓ p)) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ (varPred _ _ _ _) p mvix ix*
    ; iso = λ p mvix ix* →
        subst (λ f → View₁ f p mvix ix* ↔ View₁ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₁ (varPred _ _ _ _) p mvix ix*))
    } ,′
  let View₂ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (# here refl) (roll↓ p) mvix ix* ×
        f (here refl) (B↓ (roll↓ p)) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ (varPred _ _ _ _) p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        subst (λ f → View₂ f p mvix ix* ↔ View₂ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₂ (varPred _ _ _ _) p mvix ix*))
    }
AnnRulesMVIxPredView 𝒜 `R-cross-box (τ , τ′ , refl) tmplPred
  with TermTmplPred.varPred? tmplPred in varPred?-eq
... | nothing =
  let View₁ = TermTmplPred.boundaryPred tmplPred (here refl) (box (#(here refl))) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        subst (λ f →
                (View₁ p mvix ix* ×
                  f (here refl) (box↓ (B↓ p)) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₁ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₁ p mvix ix*)))
    } ,′
  let View₂ = λ {ϑ = ϑ} p mvix ix* →
        TermTmplPred.proxyPred tmplPred (here refl) _ (box/m (# here refl)) p mvix ix* in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ {ϑ} p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open IsSatDownwardClosed (TermTmplPred.isSatDownwardClosed tmplPred ϑ) in
        subst (λ f →
                (View₂ p mvix ix* ×
                  f (here refl) (box↓ (proxy↓ p)) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₂ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₂ {ϑ} p mvix ix*)))
    }
... | just varPred =
  let View₁ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (box (# here refl)) p mvix ix* ×
        f (here refl) (box↓ (B↓ p)) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ (varPred _ _ _ _) p mvix ix*
    ; iso = λ p mvix ix* →
        subst (λ f → View₁ f p mvix ix* ↔ View₁ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₁ (varPred _ _ _ _) p mvix ix*))
    } ,′
  let View₂ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        proxyPred (here refl) _ (box/m (# here refl)) p mvix ix* ×
        f (here refl) (box↓ (proxy↓ p)) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ (varPred _ _ _ _) p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        subst (λ f → View₂ f p mvix ix* ↔ View₂ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₂ (varPred _ _ _ _) p mvix ix*))
    }
AnnRulesMVIxPredView 𝒜 `R-cross-lam (τ , (τₐ , τᵣ) , refl) tmplPred
  with TermTmplPred.varPred? tmplPred in varPred?-eq
... | nothing =
  let View₁ = TermTmplPred.boundaryPred tmplPred (here refl) (ƛ (#(here refl))) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        subst (λ f →
                (View₁ p mvix ix* ×
                  f (here refl) (ƛ↓ (B↓ p)) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₁ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₁ p mvix ix*)))
    } ,′
  let View₂ = λ {ϑ = ϑ} p mvix ix* →
        TermTmplPred.proxyPred tmplPred (here refl) _ (ƛ/m (# here refl)) p mvix ix* in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ {ϑ} p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open IsSatDownwardClosed (TermTmplPred.isSatDownwardClosed tmplPred ϑ) in
        subst (λ f →
                (View₂ p mvix ix* ×
                  f (here refl) (ƛ↓ (proxy↓ p)) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₂ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₂ {ϑ} p mvix ix*)))
    }
... | just varPred =
  let View₁ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (ƛ (# here refl)) p mvix ix* ×
        f (here refl) (ƛ↓ (B↓ p)) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ (varPred _ _ _ _) p mvix ix*
    ; iso = λ p mvix ix* →
        subst (λ f → View₁ f p mvix ix* ↔ View₁ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₁ (varPred _ _ _ _) p mvix ix*))
    } ,′
  let View₂ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        proxyPred (here refl) _ (ƛ/m (# here refl)) p mvix ix* ×
        f (here refl) (ƛ↓ (proxy↓ p)) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ (varPred _ _ _ _) p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        subst (λ f → View₂ f p mvix ix* ↔ View₂ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₂ (varPred _ _ _ _) p mvix ix*))
    }
AnnRulesMVIxPredView 𝒜 `R-merge-box (τ , τ′ , refl) tmplPred
  with TermTmplPred.varPred? tmplPred in varPred?-eq
... | nothing =
  let View₁ = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred  (here refl) (proxy/t (there(here refl)) _ (box/m (#(here refl))))
                      p mvix ix* ×
        proxyPred (there(here refl)) _ (box/m (#(here refl)))
                  (B↓ p) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ {ϑ} p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        subst (λ f →
                (View₁ p mvix ix* ×
                  f (here refl) (box↓ (proxy↓ (B↓ p))) mvix (annIxᵗ mvix (there(here refl))))
                ↔
                View₁ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₁ p mvix ix*)))
        ↔-∘
        (↔-sym ↔-×-assoc)
    } ,′
  let View₂ = λ {ϑ = ϑ} p mvix ix* →
        TermTmplPred.proxyPred tmplPred (here refl) _ (box/m (# here refl)) p mvix ix* in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ {ϑ} p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open IsSatDownwardClosed (TermTmplPred.isSatDownwardClosed tmplPred ϑ) in
        subst (λ f →
                (View₂ p mvix ix* ×
                  f (here refl) (box↓ (proxy↓ p)) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₂ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₂ {ϑ} p mvix ix*)))
    }
... | just varPred =
  let View₂ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred  (here refl) (proxy/t (there(here refl)) _ (box/m (#(here refl))))
                      p mvix ix* ×
        proxyPred (there(here refl)) _ (box/m (#(here refl)))
                  (B↓ p) mvix (annIxᵗ mvix (here refl)) ×
        f (here refl) (box↓ (proxy↓ (B↓ p))) mvix (annIxᵗ mvix (there(here refl))) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ (varPred _ _ _ _) {ϑ} p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        subst (λ f → View₂ f p mvix ix* ↔ View₂ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₂ (varPred _ _ _ _) {ϑ} p mvix ix*))
    } ,′
  let View₂ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        proxyPred (here refl) _ (box/m (# here refl)) p mvix ix* ×
        f (here refl) (box↓ (proxy↓ p)) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ (varPred _ _ _ _) p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        subst (λ f → View₂ f p mvix ix* ↔ View₂ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₂ (varPred _ _ _ _) p mvix ix*))
    }
AnnRulesMVIxPredView 𝒜 `R-merge-lam (τ , (τₐ , τᵣ) , refl) tmplPred
  with TermTmplPred.varPred? tmplPred in varPred?-eq
... | nothing =
  let View₁ = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred  (here refl) (proxy/t (there(here refl)) _ (ƛ/m (#(here refl))))
                      p mvix ix* ×
        proxyPred (there(here refl)) _ (ƛ/m (#(here refl)))
                  (B↓ p) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ {ϑ} p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        subst (λ f →
                (View₁ p mvix ix* ×
                  f (here refl) (ƛ↓ (proxy↓ (B↓ p))) mvix (annIxᵗ mvix (there(here refl))))
                ↔
                View₁ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₁ p mvix ix*)))
        ↔-∘
        (↔-sym ↔-×-assoc)
    } ,′
  let View₂ = λ {ϑ = ϑ} p mvix ix* →
        TermTmplPred.proxyPred tmplPred (here refl) _ (ƛ/m (# here refl)) p mvix ix* in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ {ϑ} p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open IsSatDownwardClosed (TermTmplPred.isSatDownwardClosed tmplPred ϑ) in
        subst (λ f →
                (View₂ p mvix ix* ×
                  f (here refl) (ƛ↓ (proxy↓ p)) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₂ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₂ {ϑ} p mvix ix*)))
    }
... | just varPred =
  let View₂ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred  (here refl) (proxy/t (there(here refl)) _ (ƛ/m (#(here refl))))
                      p mvix ix* ×
        proxyPred (there(here refl)) _ (ƛ/m (#(here refl)))
                  (B↓ p) mvix (annIxᵗ mvix (here refl)) ×
        f (here refl) (ƛ↓ (proxy↓ (B↓ p))) mvix (annIxᵗ mvix (there(here refl))) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ (varPred _ _ _ _) {ϑ} p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        subst (λ f → View₂ f p mvix ix* ↔ View₂ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₂ (varPred _ _ _ _) {ϑ} p mvix ix*))
    } ,′
  let View₂ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        proxyPred (here refl) _ (ƛ/m (# here refl)) p mvix ix* ×
        f (here refl) (ƛ↓ (proxy↓ p)) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ (varPred _ _ _ _) p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        subst (λ f → View₂ f p mvix ix* ↔ View₂ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₂ (varPred _ _ _ _) p mvix ix*))
    }
AnnRulesMVIxPredView 𝒜 `R-proxy-unbox (τ , tt) tmplPred
  with TermTmplPred.varPred? tmplPred in varPred?-eq
... | nothing =
  let View₁ = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        proxyPred (here refl) _ (box/m (# here refl)) (unbox↓ p) mvix ix* in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open IsSatDownwardClosed (TermTmplPred.isSatDownwardClosed tmplPred ϑ) in
        subst (λ f →
                (View₁ p mvix ix* ×
                  f (here refl) (box↓ (proxy↓ (unbox↓ p))) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₁ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₁ p mvix ix*)))
    } ,′
  let View₂ = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (unbox (box (# here refl))) p mvix ix* in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open IsSatDownwardClosed (TermTmplPred.isSatDownwardClosed tmplPred ϑ) in
        subst (λ f →
                (View₂ p mvix ix* ×
                  f (here refl) (box↓ (unbox↓ (B↓ p))) mvix (annIxᵗ mvix (here refl)))
                ↔
                View₂ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (↔-×-identityˡ (↔-id (View₂ {ϑ} p mvix ix*)))
    }
... | just varPred =
  let View₁ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        proxyPred (here refl) _ (box/m (# here refl)) (unbox↓ p) mvix ix* ×
        f (here refl) (box↓ (proxy↓ (unbox↓ p))) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ (varPred _ _ _ _) p mvix ix*
    ; iso = λ p mvix ix* →
        subst (λ f → View₁ f p mvix ix* ↔ View₁ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₁ (varPred _ _ _ _) p mvix ix*))
    } ,′
  let View₂ = λ f {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        boundaryPred (here refl) (unbox (box (# here refl))) p mvix ix* ×
        f (here refl) (box↓ (unbox↓ (B↓ p))) mvix (annIxᵗ mvix (here refl)) in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₂ (varPred _ _ _ _) p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        subst (λ f → View₂ f p mvix ix* ↔ View₂ (varPred _ _ _ _) p mvix ix*)
              (sym (varPred!-just tmplPred varPred?-eq))
              (↔-id (View₂ (varPred _ _ _ _) p mvix ix*))
    }
AnnRulesMVIxPredView 𝒜 `R-proxy-β (τᵣ , τₐ) tmplPred
  with TermTmplPred.varPred? tmplPred in varPred?-eq
... | nothing =
  let View₁ = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ) in
        proxyPred (here refl) _ (ƛ/m (# here refl)) (proj₁ (app↓ p)) mvix ix* in
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* → View₁ p mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open IsSatDownwardClosed (TermTmplPred.isSatDownwardClosed tmplPred ϑ) in
        subst (λ f →
                ((View₁ p mvix ix* ×
                  f (here refl) (ƛ↓ (proxy↓ (proj₁ (app↓ p)))) mvix (annIxᵗ mvix (here refl))) ×
                 varPred! tmplPred (there(here refl)) (proj₂ (app↓ p)) mvix ix*)
                ↔
                View₁ p mvix ix*)
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (subst (λ f →
                      ((View₁ p mvix ix* ×
                        ⊤) ×
                       f (there(here refl)) (proj₂ (app↓ p)) mvix ix*)
                      ↔
                      View₁ p mvix ix*)
                    (sym (varPred!-nothing tmplPred varPred?-eq))
                    (↔-×-identityˡ (↔-×-identityˡ (↔-id (View₁ p mvix ix*)))))
    } ,′
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ)
            ixᵣ = annIxᵗ mvix (there(here refl))
            pₐ = proj₂ (app↓ (B↓ p)) in
        boundaryPred (there(here refl))
                      ((ƛ (# here refl)) · B# (here refl) ⟪ #(there(here refl)) ⟫)
                      p mvix ix* ×
        boundaryPred (here refl) (#(there(here refl))) pₐ mvix ixᵣ
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ)
            ixₐ = annIxᵗ mvix (here refl)
            ixᵣ = annIxᵗ mvix (there(here refl))
            pₐ = proj₂ (app↓ (B↓ p))
            p-f = proj₁ (app↓ (B↓ p)) in
        subst (λ f →
                ((boundaryPred (there(here refl))
                               ((ƛ (# here refl)) · B# (here refl) ⟪ #(there(here refl)) ⟫)
                               p mvix ix* ×
                  f (here refl) (ƛ↓ p-f) mvix ixᵣ) ×
                 (boundaryPred (here refl) (#(there(here refl))) pₐ mvix ixᵣ ×
                  varPred! tmplPred (there(here refl)) (B↓ pₐ) mvix ixₐ))
                ↔
                (boundaryPred (there(here refl))
                              ((ƛ (# here refl)) · B# (here refl) ⟪ #(there(here refl)) ⟫)
                              p mvix ix* ×
                 boundaryPred (here refl) (#(there(here refl))) pₐ mvix ixᵣ))
              (sym (varPred!-nothing tmplPred varPred?-eq))
              (subst (λ f →
                       ((boundaryPred (there(here refl))
                                      ((ƛ (# here refl)) · B# (here refl) ⟪ #(there(here refl)) ⟫)
                                      p mvix ix* ×
                         ⊤) ×
                        (boundaryPred (here refl) (#(there(here refl))) pₐ mvix ixᵣ ×
                         f (there(here refl)) (B↓ pₐ) mvix ixₐ))
                       ↔
                       (boundaryPred (there(here refl))
                                     ((ƛ (# here refl)) · B# (here refl) ⟪ #(there(here refl)) ⟫)
                                     p mvix ix* ×
                        boundaryPred (here refl) (#(there(here refl))) pₐ mvix ixᵣ))
                     (sym (varPred!-nothing tmplPred varPred?-eq))
                     ((↔-×-identityˡ
                       (↔-id (boundaryPred (there(here refl))
                                           ((ƛ (# here refl)) ·
                                            B# (here refl) ⟪ #(there(here refl)) ⟫)
                                           p mvix ix*)))
                      ↔-,
                      (↔-×-identityˡ
                       (↔-id (boundaryPred (here refl)
                                            (#(there(here refl)))
                                            pₐ mvix ixᵣ)))))
        ↔-∘
        (↔-sym ↔-×-assoc)
  }
... | just varPred =
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ)
            p-f = proj₁ (app↓ p)
            pₐ = proj₂ (app↓ p)
            ix-f = annIxᵗ mvix (here refl) in
        proxyPred (here refl) _ (ƛ/m (# here refl)) p-f mvix ix* ×
        varPred _ _ _ _ (here refl) (ƛ↓ (proxy↓ p-f)) mvix ix-f ×
        varPred _ _ _ _ (there(here refl)) pₐ mvix ix*
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ)
            p-f = proj₁ (app↓ p)
            pₐ = proj₂ (app↓ p)
            ix-f = annIxᵗ mvix (here refl) in
        subst (λ f →
                (proxyPred (here refl) _ (ƛ/m (# here refl)) p-f mvix ix* ×
                 varPred! tmplPred (here refl) (ƛ↓ (proxy↓ p-f)) mvix ix-f ×
                 f (there(here refl)) pₐ mvix ix*)
                ↔
                (proxyPred (here refl) _ (ƛ/m (# here refl)) p-f mvix ix* ×
                 varPred _ _ _ _ (here refl) (ƛ↓ (proxy↓ p-f)) mvix ix-f ×
                 varPred _ _ _ _ (there(here refl)) pₐ mvix ix*))
              (sym (varPred!-just tmplPred varPred?-eq))
              (subst (λ f →
                       (proxyPred (here refl) _ (ƛ/m (# here refl)) p-f mvix ix* ×
                        f (here refl) (ƛ↓ (proxy↓ p-f)) mvix ix-f ×
                        varPred _ _ _ _ (there(here refl)) pₐ mvix ix*)
                       ↔
                       (proxyPred (here refl) _ (ƛ/m (# here refl)) p-f mvix ix* ×
                        varPred _ _ _ _ (here refl) (ƛ↓ (proxy↓ p-f)) mvix ix-f ×
                        varPred _ _ _ _ (there(here refl)) pₐ mvix ix*))
                     (sym (varPred!-just tmplPred varPred?-eq))
                     (↔-id _))
        ↔-∘
        ↔-×-assoc
    } ,′
  record
    { Pred = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ)
            ixₐ = annIxᵗ mvix (here refl)
            ixᵣ = annIxᵗ mvix (there(here refl))
            pₐ = proj₂ (app↓ (B↓ p))
            p-f = proj₁ (app↓ (B↓ p)) in
        boundaryPred (there(here refl))
                               ((ƛ (# here refl)) · B# (here refl) ⟪ #(there(here refl)) ⟫)
                               p mvix ix* ×
        varPred _ _ _ _ (here refl) (ƛ↓ p-f) mvix ixᵣ ×
        boundaryPred (here refl) (#(there(here refl))) pₐ mvix ixᵣ ×
        varPred _ _ _ _ (there(here refl)) (B↓ pₐ) mvix ixₐ
    ; iso = λ {ϑ = ϑ} p mvix ix* →
        let open TermTmplPred tmplPred
            open IsSatDownwardClosed (isSatDownwardClosed ϑ)
            ixₐ = annIxᵗ mvix (here refl)
            ixᵣ = annIxᵗ mvix (there(here refl))
            pₐ = proj₂ (app↓ (B↓ p))
            p-f = proj₁ (app↓ (B↓ p)) in
        subst (λ f →
                (boundaryPred (there(here refl))
                               ((ƛ (# here refl)) · B# (here refl) ⟪ #(there(here refl)) ⟫)
                               p mvix ix* ×
                 f (here refl) (ƛ↓ p-f) mvix ixᵣ ×
                 boundaryPred (here refl) (#(there(here refl))) pₐ mvix ixᵣ ×
                 varPred! tmplPred (there(here refl)) (B↓ pₐ) mvix ixₐ)
                ↔
                (boundaryPred (there(here refl))
                               ((ƛ (# here refl)) · B# (here refl) ⟪ #(there(here refl)) ⟫)
                               p mvix ix* ×
                 varPred _ _ _ _ (here refl) (ƛ↓ p-f) mvix ixᵣ ×
                 boundaryPred (here refl) (#(there(here refl))) pₐ mvix ixᵣ ×
                 varPred _ _ _ _ (there(here refl)) (B↓ pₐ) mvix ixₐ))
              (sym (varPred!-just tmplPred varPred?-eq))
              (subst (λ f →
                       (boundaryPred (there(here refl))
                                     ((ƛ (# here refl)) ·
                                      B# (here refl) ⟪ #(there(here refl)) ⟫)
                                     p mvix ix* ×
                        varPred _ _ _ _ (here refl) (ƛ↓ p-f) mvix ixᵣ ×
                        boundaryPred (here refl) (#(there(here refl))) pₐ mvix ixᵣ ×
                        f (there(here refl)) (B↓ pₐ) mvix ixₐ)
                       ↔
                       (boundaryPred (there(here refl))
                                     ((ƛ (# here refl)) ·
                                      B# (here refl) ⟪ #(there(here refl)) ⟫)
                                     p mvix ix* ×
                        varPred _ _ _ _ (here refl) (ƛ↓ p-f) mvix ixᵣ ×
                        boundaryPred (here refl) (#(there(here refl))) pₐ mvix ixᵣ ×
                        varPred _ _ _ _ (there(here refl)) (B↓ pₐ) mvix ixₐ))
                     (sym (varPred!-just tmplPred varPred?-eq))
                     (↔-id _))
  }
