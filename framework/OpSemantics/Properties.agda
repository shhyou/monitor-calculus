{-# OPTIONS --without-K --safe #-}

module OpSemantics.Properties where

open import Utils.Misc
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import Annotation.Language
open import OpSemantics.Base

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst; trans; cong; sym)

open import Data.Unit.Base as Unit using (⊤; tt) -- needed for the number typeclass
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base using (List; []; _∷_; lookup)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

private
  variable
    𝒜 : AnnTerm
    𝒯 𝒯₁ 𝒯₂ : AnnTransit 𝒜
    Ann : AnnSig

    τ : Ty
    e e′ v : ATAnn 𝒜 ∣ [] ⊢ τ
    s s′ : ATState 𝒜


value-⟶r-impossible : ∀ {v e} → Ann ∣ v isvalof τ → ¬ (v ⟶r e)
value-⟶r-impossible (proxy/v A em)  ()
value-⟶r-impossible ⋆/v             ()
value-⟶r-impossible z/v             ()
value-⟶r-impossible (s/v iv)        ()
value-⟶r-impossible (iv₁ `,/v iv₂)  ()
value-⟶r-impossible (inl/v iv)      ()
value-⟶r-impossible (inr/v iv)      ()
value-⟶r-impossible (roll/v iv)     ()
value-⟶r-impossible (box/v iv)      ()
value-⟶r-impossible (ƛ/v e)         ()

value-ctxt-betarel-impossible : ∀ {v e s s′} → ATAnn 𝒜 ∣ v isvalof τ → ¬ (CtxtRel 𝒜 BetaRel s v s′ e)
value-ctxt-betarel-impossible (proxy/v A em) (RC-here ())
value-ctxt-betarel-impossible ⋆/v            (RC-here ())
value-ctxt-betarel-impossible z/v            (RC-here ())
value-ctxt-betarel-impossible (s/v iv)       (RC-s step)          = value-ctxt-betarel-impossible iv step
value-ctxt-betarel-impossible (iv₁ `,/v iv₂) (RC-consl step)      = value-ctxt-betarel-impossible iv₁ step
value-ctxt-betarel-impossible (iv₁ `,/v iv₂) (RC-consr iv₁′ step) = value-ctxt-betarel-impossible iv₂ step
value-ctxt-betarel-impossible (inl/v iv)     (RC-inl step)        = value-ctxt-betarel-impossible iv step
value-ctxt-betarel-impossible (inr/v iv)     (RC-inr step)        = value-ctxt-betarel-impossible iv step
value-ctxt-betarel-impossible (roll/v iv)    (RC-roll step)       = value-ctxt-betarel-impossible iv step
value-ctxt-betarel-impossible (box/v iv)     (RC-box step)        = value-ctxt-betarel-impossible iv step
value-ctxt-betarel-impossible (ƛ/v e)        (RC-here ())

value-step-impossible : ∀ {v e s s′} →
  (𝒯 : AnnTransit 𝒜) →
  (tag : RuleTag) →
  ATAnn 𝒜 ∣ v isvalof τ →
  ¬ (ATStep 𝒜 (AnnRules (ATAnn 𝒜) tag , 𝒯 tag) s v s′ e)
value-step-impossible 𝒯 `R-cross-unit  () (mkStep refl               _ (mkTerm ψ₁ refl) _ _ _)
value-step-impossible 𝒯 `R-cross-nat   () (mkStep refl               _ (mkTerm ψ₁ refl) _ _ _)
value-step-impossible 𝒯 `R-cross-cons  () (mkStep ((τ₁ , τ₂) , refl) _ (mkTerm ψ₁ refl) _ _ _)
value-step-impossible 𝒯 `R-cross-inl   () (mkStep ((τ₁ , τ₂) , refl) _ (mkTerm ψ₁ refl) _ _ _)
value-step-impossible 𝒯 `R-cross-inr   () (mkStep ((τ₁ , τ₂) , refl) _ (mkTerm ψ₁ refl) _ _ _)
value-step-impossible 𝒯 `R-cross-roll  () (mkStep (τ′ , refl)        _ (mkTerm ψ₁ refl) _ _ _)
value-step-impossible 𝒯 `R-cross-box   () (mkStep (τ′ , refl)        _ (mkTerm ψ₁ refl) _ _ _)
value-step-impossible 𝒯 `R-cross-lam   () (mkStep ((τₐ , τᵣ) , refl) _ (mkTerm ψ₁ refl) _ _ _)
value-step-impossible 𝒯 `R-merge-box   () (mkStep (τ′ , refl)        _ (mkTerm ψ₁ refl) _ _ _)
value-step-impossible 𝒯 `R-merge-lam   () (mkStep ((τₐ , τᵣ) , refl) _ (mkTerm ψ₁ refl) _ _ _)
value-step-impossible 𝒯 `R-proxy-unbox () (mkStep tt                 _ (mkTerm ψ₁ refl) _ _ _)
value-step-impossible 𝒯 `R-proxy-β     () (mkStep τₐ                 _ (mkTerm ψ₁ refl) _ _ _)

value-ctxt-steprel-impossible : ∀ {v e s s′} →
  (𝒯 : AnnTransit 𝒜) →
  (tag : RuleTag) →
  ATAnn 𝒜 ∣ v isvalof τ →
  ¬ (CtxtRel 𝒜 (ATStep 𝒜 (AnnRules (ATAnn 𝒜) tag , 𝒯 tag)) s v s′ e)
value-ctxt-steprel-impossible 𝒯 tag iv (RC-here step) =
  value-step-impossible 𝒯 tag iv step
value-ctxt-steprel-impossible 𝒯 tag (s/v iv) (RC-s step) =
  value-ctxt-steprel-impossible 𝒯 tag iv step
value-ctxt-steprel-impossible 𝒯 tag (iv₁ `,/v iv₂) (RC-consl step) =
  value-ctxt-steprel-impossible 𝒯 tag iv₁ step
value-ctxt-steprel-impossible 𝒯 tag (iv₁ `,/v iv₂) (RC-consr iv₁′ step) =
  value-ctxt-steprel-impossible 𝒯 tag iv₂ step
value-ctxt-steprel-impossible 𝒯 tag (inl/v iv) (RC-inl step) =
  value-ctxt-steprel-impossible 𝒯 tag iv step
value-ctxt-steprel-impossible 𝒯 tag (inr/v iv) (RC-inr step) =
  value-ctxt-steprel-impossible 𝒯 tag iv step
value-ctxt-steprel-impossible 𝒯 tag (box/v iv) (RC-box step) =
  value-ctxt-steprel-impossible 𝒯 tag iv step
value-ctxt-steprel-impossible 𝒯 tag (roll/v iv) (RC-roll step) =
  value-ctxt-steprel-impossible 𝒯 tag iv step

value-⟶*-refl : ∀ {𝒯 : AnnTransit 𝒜} {s s′ v e} →
  ATAnn 𝒜 ∣ v isvalof τ →
  𝒯 ⊢ s , v ⟶* s′ , e →
  e ≡ v
value-⟶*-refl iv R-refl = refl
value-⟶*-refl {𝒯 = 𝒯} iv (R-step steps step) rewrite value-⟶*-refl iv steps with step
... | R-redex step         = ⊥-elim (value-ctxt-betarel-impossible iv step)
... | R-bdr tag s₁ s′ step = ⊥-elim (value-ctxt-steprel-impossible 𝒯 tag iv step)




⟶r-deterministic : {e e₁ e₂ : Ann ∣ [] ⊢ τ} →
  e ⟶r e₁ →
  e ⟶r e₂ →
  e₁ ≡ e₂
⟶r-deterministic R-foldz            R-foldz           = refl
⟶r-deterministic (R-folds iv₁)      (R-folds iv₂)     = refl
⟶r-deterministic (R-assert iv₁)     (R-assert iv₂)    = refl
⟶r-deterministic (R-outl iv₁ iv₁′)  (R-outl iv₂ iv₂′) = refl
⟶r-deterministic (R-outr iv₁ iv₁′)  (R-outr iv₂ iv₂′) = refl
⟶r-deterministic (R-casel iv₁)      (R-casel iv₂)     = refl
⟶r-deterministic (R-caser iv₁)      (R-caser iv₂)     = refl
⟶r-deterministic (R-unbox iv₁)   (R-unbox iv₂)  = refl
⟶r-deterministic (R-β iv₁)          (R-β iv₂)         = refl
⟶r-deterministic (R-unroll iv₁)     (R-unroll iv₂)    = refl
⟶r-deterministic R-fix              R-fix             = refl
⟶r-deterministic (R-seq iv₁)        (R-seq iv₂)       = refl

ctxt-betarel-deterministic : ∀ {s₁ s₁′ s₂ s₂′} {e e₁ e₂ : ATAnn 𝒜 ∣ [] ⊢ τ} →
  CtxtRel 𝒜 BetaRel s₁ e s₁′ e₁ →
  CtxtRel 𝒜 BetaRel s₂ e s₂′ e₂ →
  e₁ ≡ e₂
ctxt-betarel-deterministic (RC-here step₁) (RC-here step₂) = ⟶r-deterministic step₁ step₂
ctxt-betarel-deterministic (RC-here R-foldz)           (RC-foldN step₂) =
  ⊥-elim (value-ctxt-betarel-impossible z/v step₂)
ctxt-betarel-deterministic (RC-here (R-folds iv₁))     (RC-foldN step₂) =
  ⊥-elim (value-ctxt-betarel-impossible (s/v iv₁) step₂)
ctxt-betarel-deterministic (RC-here (R-assert iv₁))    (RC-assert step₂) =
  ⊥-elim (value-ctxt-betarel-impossible (s/v iv₁) step₂)
ctxt-betarel-deterministic (RC-here (R-outl iv₁ iv₂))  (RC-outl step₂) =
  ⊥-elim (value-ctxt-betarel-impossible (iv₁ `,/v iv₂) step₂)
ctxt-betarel-deterministic (RC-here (R-outr iv₁ iv₂))  (RC-outr step₂) =
  ⊥-elim (value-ctxt-betarel-impossible (iv₁ `,/v iv₂) step₂)
ctxt-betarel-deterministic (RC-here (R-casel iv₁))     (RC-case step₂) =
  ⊥-elim (value-ctxt-betarel-impossible (inl/v iv₁) step₂)
ctxt-betarel-deterministic (RC-here (R-caser iv₁))     (RC-case step₂) =
  ⊥-elim (value-ctxt-betarel-impossible (inr/v iv₁) step₂)
ctxt-betarel-deterministic (RC-here (R-unbox iv₁))     (RC-unbox step₂) =
  ⊥-elim (value-ctxt-betarel-impossible iv₁ step₂)
ctxt-betarel-deterministic (RC-here (R-β iv₁))         (RC-appl step₂) =
  ⊥-elim (value-ctxt-betarel-impossible (ƛ/v _) step₂)
ctxt-betarel-deterministic (RC-here (R-β iv₁))         (RC-appr iv₂ step₂) =
  ⊥-elim (value-ctxt-betarel-impossible iv₁ step₂)
ctxt-betarel-deterministic (RC-here (R-unroll iv))     (RC-unroll step₂) =
  ⊥-elim (value-ctxt-betarel-impossible (roll/v iv) step₂)
ctxt-betarel-deterministic (RC-here (R-seq iv))        (RC-seq step₂) =
  ⊥-elim (value-ctxt-betarel-impossible iv step₂)
ctxt-betarel-deterministic (RC-foldN step₁)            (RC-here R-foldz) =
  ⊥-elim (value-ctxt-betarel-impossible z/v step₁)
ctxt-betarel-deterministic (RC-foldN step₁)            (RC-here (R-folds iv₂)) =
  ⊥-elim (value-ctxt-betarel-impossible (s/v iv₂) step₁)
ctxt-betarel-deterministic (RC-assert step₁)           (RC-here (R-assert iv₂)) =
  ⊥-elim (value-ctxt-betarel-impossible (s/v iv₂) step₁)
ctxt-betarel-deterministic (RC-outl step₁)             (RC-here (R-outl iv₂ iv₂′)) =
  ⊥-elim (value-ctxt-betarel-impossible (iv₂ `,/v iv₂′) step₁)
ctxt-betarel-deterministic (RC-outr step₁)             (RC-here (R-outr iv₂ iv₂′)) =
  ⊥-elim (value-ctxt-betarel-impossible (iv₂ `,/v iv₂′) step₁)
ctxt-betarel-deterministic (RC-case step₁)             (RC-here (R-casel iv₂)) =
  ⊥-elim (value-ctxt-betarel-impossible (inl/v iv₂) step₁)
ctxt-betarel-deterministic (RC-case step₁)             (RC-here (R-caser iv₂)) =
  ⊥-elim (value-ctxt-betarel-impossible (inr/v iv₂) step₁)
ctxt-betarel-deterministic (RC-unbox step₁)            (RC-here (R-unbox iv₂)) =
  ⊥-elim (value-ctxt-betarel-impossible iv₂ step₁)
ctxt-betarel-deterministic (RC-appl step₁)             (RC-here (R-β iv₂)) =
  ⊥-elim (value-ctxt-betarel-impossible (ƛ/v _) step₁)
ctxt-betarel-deterministic (RC-appr iv₁ step₁)         (RC-here (R-β iv₂)) =
  ⊥-elim (value-ctxt-betarel-impossible iv₂ step₁)
ctxt-betarel-deterministic (RC-unroll step₁)           (RC-here (R-unroll iv₂)) =
  ⊥-elim (value-ctxt-betarel-impossible (roll/v iv₂) step₁)
ctxt-betarel-deterministic (RC-seq step₁)              (RC-here (R-seq iv₂)) =
  ⊥-elim (value-ctxt-betarel-impossible iv₂ step₁)
ctxt-betarel-deterministic (RC-B step₁)                (RC-B step₂) =
  cong (B# _ ⟪_⟫) (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-s step₁)                (RC-s step₂) =
  cong `s (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-foldN step₁)            (RC-foldN step₂) =
  cong (λ e → foldN e _ _) (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-assert step₁)           (RC-assert step₂) =
  cong assert (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-consl step₁)            (RC-consl step₂) =
  cong (_`, _) (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-consl step₁)            (RC-consr iv₂ step₂) =
  ⊥-elim (value-ctxt-betarel-impossible iv₂ step₁)
ctxt-betarel-deterministic (RC-consr iv₁ step₁)        (RC-consl step₂) =
  ⊥-elim (value-ctxt-betarel-impossible iv₁ step₂)
ctxt-betarel-deterministic (RC-consr iv₁ step₁)        (RC-consr iv₂ step₂) =
  cong (_ `,_) (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-outl step₁)             (RC-outl step₂) =
  cong π₁ (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-outr step₁)             (RC-outr step₂) =
  cong π₂ (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-inl step₁)              (RC-inl step₂) =
  cong inl (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-inr step₁)              (RC-inr step₂) =
  cong inr (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-case step₁)             (RC-case step₂) =
  cong (case_of _ ∣ _) (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-box step₁)              (RC-box step₂) =
  cong box (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-unbox step₁)            (RC-unbox step₂) =
  cong unbox (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-appl step₁)             (RC-appl step₂) =
  cong (_· _) (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-appl step₁)             (RC-appr iv₂ step₂) =
  ⊥-elim (value-ctxt-betarel-impossible iv₂ step₁)
ctxt-betarel-deterministic (RC-appr iv₁ step₁)         (RC-appl step₂) =
  ⊥-elim (value-ctxt-betarel-impossible iv₁ step₂)
ctxt-betarel-deterministic (RC-appr iv₁ step₁)         (RC-appr iv₂ step₂) =
  cong (_ ·_) (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-unroll step₁)           (RC-unroll step₂) =
  cong unroll (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-roll step₁)             (RC-roll step₂) =
  cong (roll _) (ctxt-betarel-deterministic step₁ step₂)
ctxt-betarel-deterministic (RC-seq step₁)              (RC-seq step₂) =
  cong (_⨟ _) (ctxt-betarel-deterministic step₁ step₂)

ctxt-betarel-state-irrelevant : ∀ {s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
  ∀ s″ →
  CtxtRel 𝒜 BetaRel s  e s′ e′ →
  CtxtRel 𝒜 BetaRel s″ e s″ e′
ctxt-betarel-state-irrelevant s″ (RC-here step)     = RC-here step
ctxt-betarel-state-irrelevant s″ (RC-B step)        = RC-B (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-s step)        = RC-s (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-foldN step)    = RC-foldN (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-assert step)   = RC-assert (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-consl step)    = RC-consl (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-consr iv step) = RC-consr iv (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-outl step)     = RC-outl (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-outr step)     = RC-outr (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-inl step)      = RC-inl (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-inr step)      = RC-inr (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-case step)     = RC-case (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-box step)      = RC-box (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-unbox step)    = RC-unbox (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-appl step)     = RC-appl (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-appr iv step)  = RC-appr iv (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-unroll step)   = RC-unroll (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-roll step)     = RC-roll (ctxt-betarel-state-irrelevant s″ step)
ctxt-betarel-state-irrelevant s″ (RC-seq step)      = RC-seq (ctxt-betarel-state-irrelevant s″ step)




∅tr-ctxt-steprel-impossible : ∀ {s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
  (tag : RuleTag) →
  ¬ CtxtRel 𝒜 (ATStep 𝒜 (AnnRules (ATAnn 𝒜) tag , ∅tr tag)) s e s′ e′
∅tr-ctxt-steprel-impossible tag (RC-here step) with tag
... | `R-proxy-β = ATStep.transitWit step -- clauses fin:0-fin:10 are inferred and eliminated by Agda
∅tr-ctxt-steprel-impossible no (RC-B step)        = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-s step)        = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-foldN step)    = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-assert step)   = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-consl step)    = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-consr iv step) = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-outl step)     = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-outr step)     = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-inl step)      = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-inr step)      = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-case step)     = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-box step)      = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-unbox step)    = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-appl step)     = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-appr iv step)  = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-unroll step)   = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-roll step)     = ∅tr-ctxt-steprel-impossible no step
∅tr-ctxt-steprel-impossible no (RC-seq step)      = ∅tr-ctxt-steprel-impossible no step


∅tr-⟶-preserve-state : ∀ {s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
  (∅tr {𝒜} ⊢ s , e ⟶ s′ , e′) →
  s ≡ s′
∅tr-⟶-preserve-state (R-redex step)       = refl
∅tr-⟶-preserve-state (R-bdr no s s′ step) = ⊥-elim (∅tr-ctxt-steprel-impossible no step)

∅tr-⟶-state-irrelevant : ∀ {s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
  ∀ s″ →
  (∅tr {𝒜} ⊢ s , e ⟶ s′ , e′) →
  (∅tr {𝒜} ⊢ s″ , e ⟶ s″ , e′)
∅tr-⟶-state-irrelevant s″ (R-redex step)       = R-redex (ctxt-betarel-state-irrelevant s″ step)
∅tr-⟶-state-irrelevant s″ (R-bdr no s s′ step) = ⊥-elim (∅tr-ctxt-steprel-impossible no step)

∅tr-⟶-deterministic : ∀ {s₁ s₁′ s₂ s₂′} {e e₁ e₂ : ATAnn 𝒜 ∣ [] ⊢ τ} →
  (∅tr {𝒜} ⊢ s₁ , e ⟶ s₁′ , e₁) →
  (∅tr {𝒜} ⊢ s₂ , e ⟶ s₂′ , e₂) →
  e₁ ≡ e₂
∅tr-⟶-deterministic (R-redex step₁)         (R-redex step₂)         =
  ctxt-betarel-deterministic step₁ step₂
∅tr-⟶-deterministic (R-redex step₁)         (R-bdr no₂ s s₂ step₂)  =
  ⊥-elim (∅tr-ctxt-steprel-impossible no₂ step₂)
∅tr-⟶-deterministic (R-bdr no₁ s s₁ step₁)  step₂ =
  ⊥-elim (∅tr-ctxt-steprel-impossible no₁ step₁)




∅tr-⟶*-preserve-state : ∀ {𝒜 τ s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
  (∅tr {𝒜} ⊢ s , e ⟶* s′ , e′) →
  s ≡ s′
∅tr-⟶*-preserve-state R-refl              = refl
∅tr-⟶*-preserve-state (R-step steps step) =
  trans (∅tr-⟶*-preserve-state steps) (∅tr-⟶-preserve-state step)

∅tr-⟶*-state-irrelevant : ∀ {𝒜 τ s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
  ∀ s″ →
  (∅tr {𝒜} ⊢ s , e ⟶* s′ , e′) →
  ∅tr {𝒜} ⊢ s″ , e ⟶* s″ , e′
∅tr-⟶*-state-irrelevant s″ R-refl              = R-refl
∅tr-⟶*-state-irrelevant s″ (R-step steps step) =
  R-step (∅tr-⟶*-state-irrelevant s″ steps) (∅tr-⟶-state-irrelevant s″ step)

∅tr-⟶*-deterministic1 : ∀ {𝒜 τ s₁ s₁′ s₂ s₂′} {e e₁ e₂ : ATAnn 𝒜 ∣ [] ⊢ τ} →
  ∀ s →
  (∅tr {𝒜} ⊢ s₁ , e ⟶ s₁′ , e₁) →
  (∅tr {𝒜} ⊢ s₂ , e ⟶* s₂′ , e₂) →
  e ≡ e₂ ⊎ (∅tr {𝒜} ⊢ s , e₁ ⟶* s , e₂)
∅tr-⟶*-deterministic1 s step₁ R-refl = inj₁ refl
∅tr-⟶*-deterministic1 s step₁ (R-step steps step) with ∅tr-⟶*-deterministic1 s step₁ steps
... | inj₂ e₁⟶*e₃ = inj₂ (R-step e₁⟶*e₃ (∅tr-⟶-state-irrelevant s step))
... | inj₁ refl
  rewrite ∅tr-⟶-preserve-state step₁ | ∅tr-⟶-preserve-state step | ∅tr-⟶-deterministic step₁ step
  = inj₂ R-refl

∅tr-⟶*-deterministic : ∀ {𝒜 τ s₁ s₁′ s₂ s₂′} {e e₁ e₂ : ATAnn 𝒜 ∣ [] ⊢ τ} →
  ∀ s →
  (∅tr {𝒜} ⊢ s₁ , e ⟶* s₁′ , e₁) →
  (∅tr {𝒜} ⊢ s₂ , e ⟶* s₂′ , e₂) →
  (∅tr {𝒜} ⊢ s , e₁ ⟶* s , e₂) ⊎ (∅tr {𝒜} ⊢ s , e₂ ⟶* s , e₁)
∅tr-⟶*-deterministic s steps₁ R-refl = inj₂ (∅tr-⟶*-state-irrelevant s steps₁)
∅tr-⟶*-deterministic s steps₁ (R-step steps₂ step₂) with ∅tr-⟶*-deterministic s steps₁ steps₂
... | inj₁ e₁⟶*e₃ = inj₁ (R-step e₁⟶*e₃ (∅tr-⟶-state-irrelevant s step₂))
... | inj₂ e₃⟶*e₁ with ∅tr-⟶*-deterministic1 s step₂ e₃⟶*e₁
... | inj₁ refl = inj₁ (R-step R-refl (∅tr-⟶-state-irrelevant s step₂))
... | inj₂ e₂⟶*e₁ = inj₂ e₂⟶*e₁

value-∅tr-⟶*-deterministic : ∀ {𝒜 τ s₁ s₁′ s₂ s₂′ e v₁ v₂} →
  ATAnn 𝒜 ∣ v₁ isvalof τ →
  ATAnn 𝒜 ∣ v₂ isvalof τ →
  (∅tr {𝒜} ⊢ s₁ , e ⟶* s₁′ , v₁) →
  (∅tr {𝒜} ⊢ s₂ , e ⟶* s₂′ , v₂) →
  v₁ ≡ v₂
value-∅tr-⟶*-deterministic {s₁ = s₁} iv₁ iv₂ steps₁ steps₂ with ∅tr-⟶*-deterministic s₁ steps₁ steps₂
... | inj₁ v₁⟶*v₂ = sym (value-⟶*-refl iv₁ v₁⟶*v₂)
... | inj₂ v₂⟶*v₁ = value-⟶*-refl iv₂ v₂⟶*v₁




⟶-∩⁻ˡ : ∀ 𝒯₂ {𝒯₁ : AnnTransit 𝒜} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} {s s′} →
  (𝒯₁ ∩tr 𝒯₂) ⊢ s , e ⟶ s′ , e′ →
  𝒯₁ ⊢ s , e ⟶ s′ , e′
⟶-∩⁻ˡ {𝒜 = 𝒜} 𝒯₂ {𝒯₁} (R-redex step) = R-redex step
⟶-∩⁻ˡ {𝒜 = 𝒜} 𝒯₂ {𝒯₁} (R-bdr tag s s′ step) = R-bdr tag s s′ (map-ctxt step-∩⁻ˡ step)
  where step-∩⁻ˡ : ∀ {τ s s′ e e′} →
                    ATStep 𝒜 {τ} (AnnRules (ATAnn 𝒜) tag , (𝒯₁ ∩tr 𝒯₂) tag) s e s′ e′ →
                    ATStep 𝒜 {τ} (AnnRules (ATAnn 𝒜) tag , 𝒯₁ tag) s e s′ e′
        step-∩⁻ˡ (mkStep tyVarsWit termEnv term₁ term₂ premiseWit transitWit) =
          mkStep tyVarsWit termEnv term₁ term₂ premiseWit (proj₁ transitWit)

⟶-∩⁻ʳ : ∀ 𝒯₁ {𝒯₂ : AnnTransit 𝒜} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} {s s′} →
  (𝒯₁ ∩tr 𝒯₂) ⊢ s , e ⟶ s′ , e′ →
  𝒯₂ ⊢ s , e ⟶ s′ , e′
⟶-∩⁻ʳ {𝒜 = 𝒜} 𝒯₁ {𝒯₂} (R-redex step) = R-redex step
⟶-∩⁻ʳ {𝒜 = 𝒜} 𝒯₁ {𝒯₂} (R-bdr tag s s′ step) = R-bdr tag s s′ (map-ctxt step-∩⁻ʳ step)
  where step-∩⁻ʳ : ∀ {τ s s′ e e′} →
                    ATStep 𝒜 {τ} (AnnRules (ATAnn 𝒜) tag , (𝒯₁ ∩tr 𝒯₂) tag) s e s′ e′ →
                    ATStep 𝒜 {τ} (AnnRules (ATAnn 𝒜) tag , 𝒯₂ tag) s e s′ e′
        step-∩⁻ʳ (mkStep tyVarsWit termEnv term₁ term₂ premiseWit transitWit) =
          mkStep tyVarsWit termEnv term₁ term₂ premiseWit (proj₂ transitWit)
