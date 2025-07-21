{-# OPTIONS --without-K --safe #-}

module Annotation.Language where

open Agda.Primitive

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
import TransitionRelationUtil as TR

open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product
  using (Σ; Σ-syntax; _,_; proj₁; proj₂; ∃; ∃-syntax; _×_; _,′_)
open import Data.List.Base as List
  using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any as ListAny
  using (Any; here; there)
open import Data.List.Relation.Unary.All as ListAll
  using (All; []; _∷_)

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; module ≡-Reasoning)

open import Function.Base using (id; const; _∘′_)


private variable
  τ τ′ τ″ : Ty


record AnnTerm : Set₁ where
  inductive
  constructor mkAnnTerm
  field
    Ann : AnnSig
    State : Set

open AnnTerm public
  using ()
  renaming (Ann to ATAnn; State to ATState)


record PreRule (Ann : AnnSig) τ : Set₁ where
  inductive; no-eta-equality
  field
    preruleCtxt : List (Ctxt × Ty)
    premise : MEnv Ann preruleCtxt → Set
    termTmpl₁ : TermTmpl Ann preruleCtxt τ
    termTmpl₂ : TermTmpl Ann preruleCtxt τ

  PreTransitSig : Set → Set₁
  PreTransitSig State =
    (metavars+wit : Σ (MEnv Ann preruleCtxt) premise) →
    (anns₁ : TermTAnnEnv termTmpl₁) →
    (anns₂ : TermTAnnEnv termTmpl₂) →
    (s₁ : State) → (s₂ : State) → Set
open PreRule public
  renaming (preruleCtxt to prCtxt; premise to prPremise; termTmpl₁ to prTermTmpl₁; termTmpl₂ to prTermTmpl₂)

record Rule (Ann : AnnSig) : Set₁ where
  inductive
  constructor mkRule

  field tyVarsPred : Ty → Set
  TyVars = Σ Ty tyVarsPred

  field mkPreRule : (tyvars : TyVars) → PreRule Ann (proj₁ tyvars)

module AnnRule (𝒜 : AnnTerm) where
  open AnnTerm 𝒜

  TransitSig : Rule Ann → Set₁
  TransitSig R = (tyvars : Rule.TyVars R) → PreRule.PreTransitSig (Rule.mkPreRule R tyvars) State

  record Step {τ} (RTr : Σ (Rule Ann) TransitSig)
    (s₁ : State) (e₁ : Ann ∣ [] ⊢ τ)
    (s₂ : State) (e₂ : Ann ∣ [] ⊢ τ)
    : Set where
      constructor mkStep
      module RStep = Rule (proj₁ RTr)
      field tyVarsWit : RStep.tyVarsPred τ
      tyvars = (τ , tyVarsWit)
      TransitRel = proj₂ RTr tyvars

      open PreRule (RStep.mkPreRule tyvars) public
      field
        termEnv : MEnv Ann preruleCtxt
        term₁ : Term Ann termTmpl₁ termEnv e₁
        term₂ : Term Ann termTmpl₂ termEnv e₂
        premiseWit : premise termEnv
        transitWit : TransitRel (termEnv , premiseWit) (Term.anns term₁) (Term.anns term₂) s₁ s₂

  record PendingStep {τ} (R : Rule Ann) (e₁ : Ann ∣ [] ⊢ τ) : Set where
    constructor mkPendingStep
    field tyVarsWit : Rule.tyVarsPred R τ
    tyvars = (τ , tyVarsWit)

    open PreRule (Rule.mkPreRule R tyvars) public
    field
      termEnv : MEnv Ann preruleCtxt
      term₁ : Term Ann termTmpl₁ termEnv e₁
      premiseWit : premise termEnv

open AnnRule public
  using (mkStep; mkPendingStep)
  renaming (TransitSig to ATTransitSig; Step to ATStep; PendingStep to ATPendingStep)

Pending⇒Step : ∀ {𝒜 s₁ s₂ e₁} {RTr : Σ (Rule (ATAnn 𝒜)) (ATTransitSig 𝒜)} →
  (pending : ATPendingStep 𝒜 {τ} (proj₁ RTr) e₁) →
  let open ATPendingStep pending in
  (anns₂ : TermTAnnEnv termTmpl₂) →
  proj₂ RTr tyvars (termEnv , premiseWit) (Term.anns term₁) anns₂ s₁ s₂ →
  ATStep 𝒜 {τ} RTr s₁ e₁ s₂ (esubstᵗ (exprᵗ termTmpl₂) (mkMV anns₂ termEnv))
Pending⇒Step (mkPendingStep tyWit termEnv term₁ premWit) anns₂ transitWit =
  mkStep tyWit termEnv term₁ (mkTerm anns₂ refl) premWit transitWit

record AnnTermView (𝒜 : AnnTerm) (𝒜client : AnnTerm) : Set where
  inductive; no-eta-equality
  constructor mkView
  field
    getAnn : ∀ {τ} → ATAnn 𝒜 τ → ATAnn 𝒜client τ
    getState : ATState 𝒜 → ATState 𝒜client
    putState : ATState 𝒜client → ATState 𝒜 → ATState 𝒜
    get-put : ∀ s₁ → putState (getState s₁) s₁ ≡ s₁
    put-get : ∀ s₁ s₂ → getState (putState s₂ s₁) ≡ s₂
    put-put : ∀ s₁ s₂ s₂′ → putState s₂′ (putState s₂ s₁) ≡ putState s₂′ s₁

open AnnTermView public
  using ()
  renaming (getAnn to getATAnn; getState to getATState; putState to putATState)

annTermViewCompose : ∀ {𝒜 𝒜₁ 𝒜₂ : AnnTerm} → AnnTermView 𝒜₁ 𝒜₂ → AnnTermView 𝒜 𝒜₁ → AnnTermView 𝒜 𝒜₂
annTermViewCompose v₂ v₁ = mkView (getATAnn v₂ ∘′ getATAnn v₁)
                                  (getATState v₂ ∘′ getATState v₁)
                                  (λ s S →
                                    putATState  v₁
                                                (putATState v₂ s (getATState v₁ S))
                                                S)
                                  (λ S → begin
                                    putATState  v₁
                                                (putATState v₂
                                                            (getATState v₂ (getATState v₁ S))
                                                            (getATState v₁ S))
                                                S
                                      ≡⟨ cong (λ s → putATState v₁ s S)
                                              (AnnTermView.get-put v₂ (getATState v₁ S)) ⟩
                                    putATState  v₁
                                                (getATState v₁ S)
                                                S
                                      ≡⟨ AnnTermView.get-put v₁ S ⟩
                                    S ∎)
                                  (λ S s → begin
                                    getATState v₂
                                      (getATState v₁
                                        (putATState v₁
                                                    (putATState v₂ s (getATState v₁ S))
                                                    S))
                                      ≡⟨ cong (getATState v₂)
                                              (AnnTermView.put-get v₁
                                                                   S
                                                                   (putATState v₂ s (getATState v₁ S))) ⟩
                                    getATState v₂ (putATState v₂ s (getATState v₁ S))
                                      ≡⟨ AnnTermView.put-get v₂ (getATState v₁ S) s ⟩
                                    s ∎)
                                  (λ S s s′ → begin
                                    putATState v₁
                                        (putATState v₂
                                                    s′
                                                    (getATState v₁
                                                      (putATState v₁
                                                                  (putATState v₂ s (getATState v₁ S))
                                                                  S)))
                                        (putATState v₁ (putATState v₂ s (getATState v₁ S)) S)
                                      ≡⟨ cong (λ s₃ →
                                                putATState v₁
                                                  (putATState v₂ s′ s₃)
                                                  (putATState v₁ (putATState v₂ s (getATState v₁ S)) S))
                                              (AnnTermView.put-get  v₁
                                                                    S
                                                                    (putATState v₂ s (getATState v₁ S))) ⟩
                                    putATState v₁
                                        (putATState v₂ s′ (putATState v₂ s (getATState v₁ S)))
                                        (putATState v₁ (putATState v₂ s (getATState v₁ S)) S)
                                      ≡⟨ cong (λ s₃ →
                                                putATState v₁
                                                  s₃
                                                  (putATState v₁ (putATState v₂ s (getATState v₁ S)) S))
                                              (AnnTermView.put-put v₂ (getATState v₁ S) s s′) ⟩
                                    putATState v₁
                                        (putATState v₂ s′ (getATState v₁ S))
                                        (putATState v₁ (putATState v₂ s (getATState v₁ S)) S)
                                      ≡⟨ AnnTermView.put-put  v₁
                                                              S
                                                              (putATState v₂ s (getATState v₁ S))
                                                              (putATState v₂ s′ (getATState v₁ S)) ⟩
                                    putATState v₁ (putATState v₂ s′ (getATState v₁ S)) S ∎)
  where open ≡-Reasoning

module AnnTermViewUtils {𝒜 𝒜client : AnnTerm} (𝒜view : AnnTermView 𝒜 𝒜client) where
  open AnnTermView 𝒜view public

  liftStateRel : (ATState 𝒜client → ATState 𝒜client → Set) → (ATState 𝒜 → ATState 𝒜 → Set)
  liftStateRel state-rel s s′ = state-rel (getState s) (getState s′)

  guardState : ATState 𝒜client → (ATState 𝒜 → ATState 𝒜 → Set)
  guardState stat = TR._∩_ (ATState 𝒜) (liftStateRel (λ s s′ → s ≡ stat)) (TR.id (ATState 𝒜))

  infix 1 withAnnView1
  infix 1 withAnnView2
  infix 1 withAnnView3
  syntax withAnnView1 A (λ a → st) = getAnn[ a ← A ] st
  syntax withAnnView2 A₁ A₂ (λ a₁ a₂ → st) = getAnn[ a₁ , a₂ ← A₁ , A₂ ] st
  syntax withAnnView3 A₁ A₂ A₃ (λ a₁ a₂ a₃ → st) = getAnn[ a₁ , a₂ , a₃ ← A₁ , A₂ , A₃ ] st

  withAnnView1 : ATAnn 𝒜 τ →
                 (ATAnn 𝒜client τ → Set) →
                 Set
  withAnnView1 A  ann-rel = ann-rel (getAnn A)

  withAnnView2 : ATAnn 𝒜 τ → ATAnn 𝒜 τ′ →
                 (ATAnn 𝒜client τ → ATAnn 𝒜client τ′ → Set) →
                 Set
  withAnnView2 A₁ A₂ ann-rel = ann-rel (getAnn A₁) (getAnn A₂)

  withAnnView3 : ATAnn 𝒜 τ → ATAnn 𝒜 τ′ → ATAnn 𝒜 τ″ →
                 (ATAnn 𝒜client τ → ATAnn 𝒜client τ′ → ATAnn 𝒜client τ″ → Set) →
                 Set
  withAnnView3 A₁ A₂ A₃ ann-rel = ann-rel (getAnn A₁) (getAnn A₂) (getAnn A₃)

id𝒜view : ∀ {𝒜} → AnnTermView 𝒜 𝒜
id𝒜view = mkView id id const (λ s₁ → refl) (λ s₁ s₂ → refl) (λ s₁ s₂ s₂′ → refl)

data RuleTag : Set where
  `R-cross-unit : RuleTag
  `R-cross-nat : RuleTag
  `R-cross-cons : RuleTag
  `R-cross-inl : RuleTag
  `R-cross-inr : RuleTag
  `R-cross-roll : RuleTag
  `R-cross-box : RuleTag
  `R-cross-lam : RuleTag
  `R-merge-box : RuleTag
  `R-merge-lam : RuleTag
  `R-proxy-unbox : RuleTag
  `R-proxy-β : RuleTag

R-cross-unit R-cross-nat R-cross-cons R-cross-inl R-cross-inr R-cross-roll : ∀ Ann → Rule Ann
R-cross-box R-cross-lam R-merge-box R-merge-lam : ∀ Ann → Rule Ann
R-proxy-unbox R-proxy-β : ∀ Ann → Rule Ann

AnnRules : ∀ Ann → RuleTag → Rule Ann
AnnRules Ann `R-cross-unit = R-cross-unit Ann
AnnRules Ann `R-cross-nat = R-cross-nat Ann
AnnRules Ann `R-cross-cons = R-cross-cons Ann
AnnRules Ann `R-cross-inl = R-cross-inl Ann
AnnRules Ann `R-cross-inr = R-cross-inr Ann
AnnRules Ann `R-cross-roll = R-cross-roll Ann
AnnRules Ann `R-cross-box = R-cross-box Ann
AnnRules Ann `R-cross-lam = R-cross-lam Ann
AnnRules Ann `R-merge-box = R-merge-box Ann
AnnRules Ann `R-merge-lam = R-merge-lam Ann
AnnRules Ann `R-proxy-unbox = R-proxy-unbox Ann
AnnRules Ann `R-proxy-β = R-proxy-β Ann

AnnTransit : (𝒜 : AnnTerm) → Set₁
AnnTransit 𝒜 = (tag : RuleTag) → ATTransitSig 𝒜 (AnnRules (ATAnn 𝒜) tag)

∅tr : ∀ {𝒜} → AnnTransit 𝒜
∅tr {𝒜} tag tyvars premWit ψ₁ ψ₂ = TR.∅ (ATState 𝒜)

infixr 7 _∩tr_
infixr 9 _∘tr_

_∩tr_ : ∀ {𝒜} → AnnTransit 𝒜 → AnnTransit 𝒜 → AnnTransit 𝒜
_∩tr_ {𝒜} 𝒯₁ 𝒯₂ tag ϑ+witness premwit anns₁ anns₂ s₁ s₂ =
  𝒯₁ tag ϑ+witness premwit anns₁ anns₂ s₁ s₂ ×
  𝒯₂ tag ϑ+witness premwit anns₁ anns₂ s₁ s₂

_∘tr_ : ∀ {𝒜} → AnnTransit 𝒜 → AnnTransit 𝒜 → AnnTransit 𝒜
_∘tr_ {𝒜} 𝒯₁ 𝒯₂ tag ϑ+witness premwit anns₁ anns₂ s₁ s₃ =
  Σ (ATState 𝒜) λ s₂ →
    𝒯₁ tag ϑ+witness premwit anns₁ anns₂ s₁ s₂ ×
    𝒯₂ tag ϑ+witness premwit anns₁ anns₂ s₂ s₃

{-
R-cross-X : Rule
Rule.tyVarsPred R-cross-X τ = ?
Rule.mkPreRule  R-cross-X (τ , pf) = crossYPR where
  crossYPR : PreRule τ
  prCtxt crossYPR = {!   !}
  prPremise crossYPR ϑ = {!   !}
  annCtxt (prTermTmpl₁ crossYPR) = {!   !}
  exprᵗ   (prTermTmpl₁ crossYPR) = {!   !}
  annCtxt (prTermTmpl₂ crossYPR) = {!   !}
  exprᵗ   (prTermTmpl₂ crossYPR) = {!   !}
-}

Rule.tyVarsPred (R-cross-unit Ann) τ = (τ ≡ `1)
Rule.mkPreRule  (R-cross-unit Ann) (.`1 , refl) = crossUnitPR where
  crossUnitPR : PreRule Ann `1
  prCtxt crossUnitPR   = []
  prPremise  crossUnitPR ϑ = ⊤
  annCtxt (prTermTmpl₁ crossUnitPR) = `1 ∷ []
  exprᵗ   (prTermTmpl₁ crossUnitPR) = B# (here refl) ⟪ ⋆ ⟫
  annCtxt (prTermTmpl₂ crossUnitPR) = []
  exprᵗ   (prTermTmpl₂ crossUnitPR) = ⋆

Rule.tyVarsPred (R-cross-nat Ann) τ = (τ ≡ `ℕ)
Rule.mkPreRule  (R-cross-nat Ann) (.`ℕ , refl) = crossNatPR where
  crossNatPR : PreRule Ann `ℕ
  prCtxt crossNatPR   = ([] ,′ `ℕ) ∷ []
  prPremise  crossNatPR ϑ = Ann ∣ ϑ(here refl) isvalof `ℕ
  annCtxt (prTermTmpl₁ crossNatPR) = `ℕ ∷ []
  exprᵗ   (prTermTmpl₁ crossNatPR) = B# (here refl) ⟪ #(here refl) ⟫
  annCtxt (prTermTmpl₂ crossNatPR) = []
  exprᵗ   (prTermTmpl₂ crossNatPR) = #(here refl)

Rule.tyVarsPred (R-cross-cons Ann) τ = ∃ λ τs → τ ≡ (proj₁ τs `* proj₂ τs)
Rule.mkPreRule  (R-cross-cons Ann) (.(τ₁ `* τ₂) , (τ₁ , τ₂) , refl) = crossConsPR where
  crossConsPR : PreRule Ann (τ₁ `* τ₂)
  prCtxt crossConsPR   = ([] ,′ τ₁) ∷ ([] ,′ τ₂) ∷ []
  prPremise  crossConsPR ϑ =
    (Ann ∣ ϑ(here refl) isvalof τ₁) ×
    (Ann ∣ ϑ(there (here refl)) isvalof τ₂)
  annCtxt (prTermTmpl₁ crossConsPR) = (τ₁ `* τ₂) ∷ []
  exprᵗ   (prTermTmpl₁ crossConsPR) = B# (here refl) ⟪ #(here refl) `, #(there (here refl)) ⟫
  annCtxt (prTermTmpl₂ crossConsPR) = τ₁ ∷ τ₂ ∷ []
  exprᵗ   (prTermTmpl₂ crossConsPR) = B# (here refl) ⟪ #(here refl) ⟫ `,
                                     B# (there (here refl)) ⟪ #(there (here refl)) ⟫

Rule.tyVarsPred (R-cross-inl Ann) τ = ∃ λ τs → τ ≡ (proj₁ τs `+ proj₂ τs)
Rule.mkPreRule  (R-cross-inl Ann) (.(τ₁ `+ τ₂) , (τ₁ , τ₂) , refl) = crossInlPR where
  crossInlPR : PreRule Ann (τ₁ `+ τ₂)
  prCtxt crossInlPR = ([] ,′ τ₁) ∷ []
  prPremise crossInlPR ϑ = Ann ∣ ϑ(here refl) isvalof τ₁
  annCtxt (prTermTmpl₁ crossInlPR) = (τ₁ `+ τ₂) ∷ []
  exprᵗ   (prTermTmpl₁ crossInlPR) = B# (here refl) ⟪ inl (# here refl) ⟫
  annCtxt (prTermTmpl₂ crossInlPR) = τ₁ ∷ []
  exprᵗ   (prTermTmpl₂ crossInlPR) = inl (B# (here refl) ⟪ (# here refl) ⟫)

Rule.tyVarsPred (R-cross-inr Ann) τ = ∃ λ τs → τ ≡ (proj₁ τs `+ proj₂ τs)
Rule.mkPreRule  (R-cross-inr Ann) (.(τ₁ `+ τ₂) , (τ₁ , τ₂) , refl) = crossInrPR where
  crossInrPR : PreRule Ann (τ₁ `+ τ₂)
  prCtxt crossInrPR = ([] ,′ τ₂) ∷ []
  prPremise crossInrPR ϑ = Ann ∣ ϑ(here refl) isvalof τ₂
  annCtxt (prTermTmpl₁ crossInrPR) = (τ₁ `+ τ₂) ∷ []
  exprᵗ   (prTermTmpl₁ crossInrPR) = B# (here refl) ⟪ inr (# here refl) ⟫
  annCtxt (prTermTmpl₂ crossInrPR) = τ₂ ∷ []
  exprᵗ   (prTermTmpl₂ crossInrPR) = inr (B# (here refl) ⟪ (# here refl) ⟫)

Rule.tyVarsPred (R-cross-roll Ann) τ = ∃[ τ′ ] τ ≡ μ τ′
Rule.mkPreRule  (R-cross-roll Ann) (.(μ τ′) , τ′ , refl) = crossRollPR where
  τᵤ = tsubst τ′ [t0↦ μ τ′ ]

  crossRollPR : PreRule Ann (μ τ′)
  prCtxt crossRollPR = ([] ,′ τᵤ) ∷ []
  prPremise crossRollPR ϑ = Ann ∣ ϑ(here refl) isvalof τᵤ
  annCtxt (prTermTmpl₁ crossRollPR) = μ τ′ ∷ []
  exprᵗ   (prTermTmpl₁ crossRollPR) = B# (here refl) ⟪ roll τ′ (# here refl) ⟫
  annCtxt (prTermTmpl₂ crossRollPR) = τᵤ ∷ []
  exprᵗ   (prTermTmpl₂ crossRollPR) = roll τ′ (B# (here refl) ⟪ (# here refl) ⟫)

Rule.tyVarsPred (R-cross-box Ann) τ = ∃ λ τ′ → τ ≡ Box τ′
Rule.mkPreRule  (R-cross-box Ann) (.(Box τ′) , τ′ , refl) = crossBoxPR where
  crossBoxPR : PreRule Ann (Box τ′)
  prCtxt crossBoxPR = ([] ,′ τ′) ∷ []
  prPremise crossBoxPR ϑ = (Ann ∣ ϑ(here refl) isvalof τ′)
  annCtxt (prTermTmpl₁ crossBoxPR) = Box τ′ ∷ []
  exprᵗ   (prTermTmpl₁ crossBoxPR) = B# (here refl) ⟪ box (# here refl) ⟫
  annCtxt (prTermTmpl₂ crossBoxPR) = Box τ′ ∷ []
  exprᵗ   (prTermTmpl₂ crossBoxPR) = proxy/t (here refl) _ (box/m (# here refl))

Rule.tyVarsPred (R-cross-lam Ann) τ = ∃ λ τs → τ ≡ proj₁ τs `→ proj₂ τs
Rule.mkPreRule  (R-cross-lam Ann) (.(τₐ `→ τᵣ) , (τₐ , τᵣ) , refl) = crossLamPR where
  crossLamPR : PreRule Ann (τₐ `→ τᵣ)
  prCtxt crossLamPR = (τₐ ∷ [] ,′ τᵣ) ∷ []
  prPremise crossLamPR ϑ = ⊤
  annCtxt (prTermTmpl₁ crossLamPR) = (τₐ `→ τᵣ) ∷ []
  exprᵗ   (prTermTmpl₁ crossLamPR) = B# (here refl) ⟪ (ƛ #(here refl)) ⟫
  annCtxt (prTermTmpl₂ crossLamPR) = (τₐ `→ τᵣ) ∷ []
  exprᵗ   (prTermTmpl₂ crossLamPR) = proxy/t (here refl) _ (ƛ/m #(here refl))

Rule.tyVarsPred (R-merge-box Ann) τ = ∃ λ τ′ → τ ≡ Box τ′
Rule.mkPreRule  (R-merge-box Ann) (.(Box τ′) , τ′ , refl) = mergeBoxPR where
  mergeBoxPR : PreRule Ann (Box τ′)
  prCtxt mergeBoxPR = ([] ,′ τ′) ∷ []
  prPremise mergeBoxPR ϑ = ⊤ -- Ann ∣ ϑ(here refl) isvalof τ′ -- similar to R-proxy-unbox
  annCtxt (prTermTmpl₁ mergeBoxPR) = (Box τ′) ∷ (Box τ′) ∷ []
  exprᵗ   (prTermTmpl₁ mergeBoxPR) = B# (here refl) ⟪ proxy/t (there (here refl)) _ (box/m (# here refl)) ⟫
  annCtxt (prTermTmpl₂ mergeBoxPR) = (Box τ′) ∷ []
  exprᵗ   (prTermTmpl₂ mergeBoxPR) = proxy/t (here refl) _ (box/m (# here refl))

Rule.tyVarsPred (R-merge-lam Ann) τ = ∃ λ τs → τ ≡ proj₁ τs `→ proj₂ τs
Rule.mkPreRule  (R-merge-lam Ann) (.(τₐ `→ τᵣ) , (τₐ , τᵣ) , refl) = mergeLamPR where
  mergeLamPR : PreRule Ann (τₐ `→ τᵣ)
  prCtxt mergeLamPR = (τₐ ∷ [] ,′ τᵣ) ∷ []
  prPremise mergeLamPR ϑ = ⊤
  annCtxt (prTermTmpl₁ mergeLamPR) = (τₐ `→ τᵣ) ∷ (τₐ `→ τᵣ) ∷ []
  exprᵗ   (prTermTmpl₁ mergeLamPR) = B# (here refl) ⟪ proxy/t (there (here refl)) _ (ƛ/m (# here refl)) ⟫
  annCtxt (prTermTmpl₂ mergeLamPR) = (τₐ `→ τᵣ) ∷ []
  exprᵗ   (prTermTmpl₂ mergeLamPR) = proxy/t (here refl) _ (ƛ/m (# here refl))

Rule.tyVarsPred (R-proxy-unbox Ann) τ = ⊤
Rule.mkPreRule  (R-proxy-unbox Ann) (τ , tt) = proxyCheckboxPR where
  proxyCheckboxPR : PreRule Ann τ
  prCtxt proxyCheckboxPR = ([] ,′ τ) ∷ []
  prPremise proxyCheckboxPR ϑ = ⊤ -- Ann ∣ ϑ(here refl) isvalof τ
  annCtxt (prTermTmpl₁ proxyCheckboxPR) = Box τ ∷ []
  exprᵗ   (prTermTmpl₁ proxyCheckboxPR) = unbox (proxy/t (here refl) _ (box/m (# here refl)))
  annCtxt (prTermTmpl₂ proxyCheckboxPR) = τ ∷ []
  exprᵗ   (prTermTmpl₂ proxyCheckboxPR) = B# (here refl) ⟪ unbox (box (# here refl)) ⟫

Rule.tyVarsPred (R-proxy-β Ann) τᵣ = Ty
Rule.mkPreRule  (R-proxy-β Ann) (τᵣ , τₐ) = proxyβPR where
  proxyβPR : PreRule Ann τᵣ
  prCtxt proxyβPR = (τₐ ∷ [] ,′ τᵣ) ∷ ([] ,′ τₐ) ∷ []
  prPremise proxyβPR ϑ = Ann ∣ ϑ(there (here refl)) isvalof τₐ
  annCtxt (prTermTmpl₁ proxyβPR) = (τₐ `→ τᵣ) ∷ []
  exprᵗ   (prTermTmpl₁ proxyβPR) = proxy/t (here refl) _ (ƛ/m #(here refl)) · #(there (here refl))
  annCtxt (prTermTmpl₂ proxyβPR) = τₐ ∷ τᵣ ∷ []
  exprᵗ   (prTermTmpl₂ proxyβPR) = B# (there (here refl)) ⟪
                                    (ƛ #(here refl)) ·
                                    B# (here refl) ⟪ #(there (here refl)) ⟫
                                  ⟫
