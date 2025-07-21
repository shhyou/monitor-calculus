{-# OPTIONS --without-K --safe #-}

module OpSemantics.TypeSafety where

open import Utils.Misc
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Language

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt) -- needed for the number typeclass
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_ ; _,′_)

open import Data.List.Base using (List; []; _∷_; lookup)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)

open import Function.Base using (_∋_; id; _∘_)

private variable
  𝒜 : AnnTerm
  τ τᵣ : Ty

data Progress {𝒜} : (s : ATState 𝒜) → (e : ATAnn 𝒜 ∣ [] ⊢ τ) → Set where
  P-step : ∀ {s} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    (step  :  CtxtRel 𝒜 BetaRel s e s e′) →
    Progress s e

  P-pending : ∀ {s e eᵣ} →
    (ec    :  ATAnn 𝒜 ∣ e ⦂ τ ▷ eᵣ ⦂ τᵣ ) →
    (tag   :  RuleTag) →
    (pending : ATPendingStep 𝒜 (AnnRules (ATAnn 𝒜) tag) eᵣ) →
    Progress s e

  P-err : ∀ {s e} →
    (ec    :  ATAnn 𝒜 ∣ e ⦂ τ ▷ (assert `z) ⦂ `1) →
    Progress s e

  P-val : ∀ {s e} →
    (iv    :  ATAnn 𝒜 ∣ e isvalof τ) →
    Progress s e

progress : (s : ATState 𝒜) → (e : ATAnn 𝒜 ∣ [] ⊢ τ) → Progress s e
progress s (proxy A em) = P-val (proxy/v A em)
progress s (B# A ⟪ e ⟫) with progress s e
... | P-step step = P-step (RC-B step)
... | P-pending ec tag pending-step = P-pending (B# A ⟪ ec ⟫) tag pending-step
... | P-err ec = P-err (B# A ⟪ ec ⟫)
... | P-val (proxy/v A′ (box/m eₘ)) = P-pending (E-here refl refl)
  `R-merge-box
  (mkPendingStep  (_ , refl)
                  (λ where (here refl) → eₘ)
                  (mkTerm (λ where
                            (here refl) → A
                            (there (here refl)) → A′)
                          refl)
                  tt) -- proxies are no longer syntactically value; see ee2a66a725 and 0090e48
... | P-val (proxy/v A′ (ƛ/m eb)) = P-pending (E-here refl refl)
  `R-merge-lam
  (mkPendingStep  (_ , refl)
                  (λ where (here refl) → eb)
                  (mkTerm (λ where
                            (here refl) → A
                            (there (here refl)) → A′)
                          refl)
                  tt) -- proxies are no longer syntactically value (ee2a66a725)
... | P-val ⋆/v = P-pending (E-here refl refl)
  `R-cross-unit
  (mkPendingStep  refl
                  (λ ())
                  (mkTerm (λ where (here refl) → A) refl)
                  tt)
... | P-val z/v = P-pending (E-here refl refl)
  `R-cross-nat
  (mkPendingStep  refl
                  (λ where (here refl) → `z)
                  (mkTerm (λ where (here refl) → A) refl)
                  z/v)
... | P-val (s/v iv) = P-pending (E-here refl refl)
  `R-cross-nat
  (mkPendingStep  refl
                  (λ where (here refl) → `s ⌊ iv ⌋v)
                  (mkTerm (λ where (here refl) → A) refl)
                  (s/v iv))
... | P-val (iv₁ `,/v iv₂) = P-pending (E-here refl refl)
  `R-cross-cons
  (mkPendingStep  (_ , refl)
                  (λ where
                    (here refl) → ⌊ iv₁ ⌋v
                    (there (here refl)) → ⌊ iv₂ ⌋v)
                  (mkTerm (λ where (here refl) → A) refl)
                  (iv₁ ,′ iv₂))
... | P-val (inl/v iv) = P-pending (E-here refl refl)
  `R-cross-inl
  (mkPendingStep  (_ , refl)
                  (λ where (here refl) → ⌊ iv ⌋v)
                  (mkTerm (λ where (here refl) → A) refl)
                  iv)
... | P-val (inr/v iv) = P-pending (E-here refl refl)
  `R-cross-inr
  (mkPendingStep  (_ , refl)
                  (λ where (here refl) → ⌊ iv ⌋v)
                  (mkTerm (λ where (here refl) → A) refl)
                  iv)
... | P-val (roll/v iv) = P-pending (E-here refl refl)
  `R-cross-roll
  (mkPendingStep  (_ , refl)
                  (λ where (here refl) → ⌊ iv ⌋v)
                  (mkTerm (λ where (here refl) → A) refl)
                  iv)
... | P-val (box/v iv) = P-pending (E-here refl refl)
  `R-cross-box
  (mkPendingStep  (_ , refl)
                  (λ where (here refl) → ⌊ iv ⌋v)
                  (mkTerm (λ where (here refl) → A) refl)
                  iv)
... | P-val (ƛ/v e) = P-pending (E-here refl refl)
  `R-cross-lam
  (mkPendingStep  (_ , refl)
                  (λ where (here refl) → e)
                  (mkTerm (λ where (here refl) → A) refl)
                  tt)
progress s ⋆ = P-val ⋆/v
progress s `z = P-val z/v
progress s (`s e) with progress s e
... | P-step step = P-step (RC-s step)
... | P-pending ec tag pending-step = P-pending (`s ec) tag pending-step
... | P-err ec = P-err (`s ec)
... | P-val iv = P-val (s/v iv)
progress s (foldN e ez es) with progress s e
... | P-step step = P-step (RC-foldN step)
... | P-pending ec tag pending-step = P-pending (foldN ec ez es) tag pending-step
... | P-err ec = P-err (foldN ec ez es)
... | P-val z/v = P-step (RC-here R-foldz)
... | P-val (s/v iv) = P-step (RC-here (R-folds iv))
progress s (assert e) with progress s e
... | P-step step = P-step (RC-assert step)
... | P-pending ec tag pending-step = P-pending (assert ec) tag pending-step
... | P-err ec = P-err (assert ec)
... | P-val z/v = P-err (E-here refl refl)
... | P-val (s/v iv) = P-step (RC-here (R-assert iv))
progress s (e₁ `, e₂) with progress s e₁
... | P-step step = P-step (RC-consl step)
... | P-pending ec tag pending-step = P-pending (ec `,ˡ e₂) tag pending-step
... | P-err ec = P-err (ec `,ˡ e₂)
... | P-val iv₁ with progress s e₂
... | P-step step = P-step (RC-consr iv₁ step)
... | P-pending ec tag pending-step = P-pending (iv₁ `,ʳ ec) tag pending-step
... | P-err ec = P-err (iv₁ `,ʳ ec)
... | P-val iv₂ = P-val (iv₁ `,/v iv₂)
progress s (π₁ e) with progress s e
... | P-step step = P-step (RC-outl step)
... | P-pending ec tag pending-step = P-pending (π₁ ec) tag pending-step
... | P-err ec = P-err (π₁ ec)
... | P-val (iv₁ `,/v iv₂) = P-step (RC-here (R-outl iv₁ iv₂))
progress s (π₂ e) with progress s e
... | P-step step = P-step (RC-outr step)
... | P-pending ec tag pending-step = P-pending (π₂ ec) tag pending-step
... | P-err ec = P-err (π₂ ec)
... | P-val (iv₁ `,/v iv₂) = P-step (RC-here (R-outr iv₁ iv₂))
progress s (inl e) with progress s e
... | P-step step = P-step (RC-inl step)
... | P-pending ec tag pending-step = P-pending (inl ec) tag pending-step
... | P-err ec = P-err (inl ec)
... | P-val iv = P-val (inl/v iv)
progress s (inr e) with progress s e
... | P-step step = P-step (RC-inr step)
... | P-pending ec tag pending-step = P-pending (inr ec) tag pending-step
... | P-err ec = P-err (inr ec)
... | P-val iv = P-val (inr/v iv)
progress s (case e of e₁ ∣ e₂) with progress s e
... | P-step step = P-step (RC-case step)
... | P-pending ec tag pending-step = P-pending (case ec of e₁ ∣ e₂) tag pending-step
... | P-err ec = P-err (case ec of e₁ ∣ e₂)
... | P-val (inl/v iv) = P-step (RC-here (R-casel iv))
... | P-val (inr/v iv) = P-step (RC-here (R-caser iv))
progress s (box e) with progress s e
... | P-step step = P-step (RC-box step)
... | P-pending ec tag pending-step = P-pending (box ec) tag pending-step
... | P-err ec = P-err (box ec)
... | P-val iv = P-val (box/v iv)
progress {τ = τ} s (unbox e) with progress s e
... | P-step step = P-step (RC-unbox step)
... | P-pending ec tag pending-step = P-pending (unbox ec) tag pending-step
... | P-err ec = P-err (unbox ec)
... | P-val (box/v iv) = P-step (RC-here (R-unbox (box/v iv)))
... | P-val (proxy/v A (box/m eₘ)) = P-pending (E-here refl refl)
  `R-proxy-unbox
  (mkPendingStep  tt
                  (λ where (here refl) → eₘ)
                  (mkTerm (λ where (here refl) → A) refl)
                  tt)
progress s (ƛ e) = P-val (ƛ/v e)
progress {τ = τᵣ} s (e · eₐ) with progress s e
... | P-step step = P-step (RC-appl step)
... | P-pending ec tag pending-step = P-pending (ec ·ˡ eₐ) tag pending-step
... | P-err ec = P-err (ec ·ˡ eₐ)
... | P-val iv with progress s eₐ
... | P-step step = P-step (RC-appr iv step)
... | P-pending ec tag pending-step = P-pending (iv ·ʳ ec) tag pending-step
... | P-err ec = P-err (iv ·ʳ ec)
... | P-val ivₐ with iv
... | ƛ/v eb = P-step (RC-here (R-β ivₐ))
... | proxy/v {τ = τₐ `→ .τᵣ} A (ƛ/m eb) = P-pending (E-here refl refl)
  `R-proxy-β
  (mkPendingStep  τₐ
                  (λ where
                    (here refl) → eb
                    (there (here refl)) → eₐ)
                  (mkTerm (λ where (here refl) → A) refl)
                  ivₐ)
progress s (unroll e) with progress s e
... | P-step step = P-step (RC-unroll step)
... | P-pending ec tag pending-step = P-pending (unroll ec) tag pending-step
... | P-err ec = P-err (unroll ec)
... | P-val (roll/v iv) = P-step (RC-here (R-unroll iv))
progress s (roll τ e) with progress s e
... | P-step step = P-step (RC-roll step)
... | P-pending ec tag pending-step = P-pending (roll τ ec) tag pending-step
... | P-err ec = P-err (roll τ ec)
... | P-val iv = P-val (roll/v iv)
progress s (fix e) = P-step (RC-here R-fix)
progress s (e ⨟ e₁) with progress s e
... | P-step step = P-step (RC-seq step)
... | P-pending ec tag pending-step = P-pending (ec ⨟ e₁) tag pending-step
... | P-err ec = P-err (ec ⨟ e₁)
... | P-val iv = P-step (RC-here (R-seq iv))
