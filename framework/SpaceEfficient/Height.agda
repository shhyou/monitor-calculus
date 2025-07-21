{-# OPTIONS --safe --without-K #-}

open import Annotation.Language

module SpaceEfficient.Height (Label : Set) (𝒜 : AnnTerm) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst; sym; trans; cong; module ≡-Reasoning)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; pred; _+_; _≤_; z≤n; s≤s;  _⊔_)
open import Data.Nat.Properties as Nat
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_; ∃₂)

open import Data.List.Base as List using (List; []; _∷_; length; map)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Syntax.Type
open import Syntax.Term

open import Contract.Common Label
open import Contract.Base Label 𝒜
  using (SCtc1N; SCtc1; flat)
open import SpaceEfficient.Base Label 𝒜

open AnnTerm 𝒜 using (Ann; State)

data SECtcMaxH : ∀ {Δ τ} → SECtcN Δ τ → ℕ → Set where
  `_ : ∀ {h Δ} → (a : tt ∈ Δ) → SECtcMaxH {Δ} (` a) h
  1/h : ∀ {h Δ} → SECtcMaxH {Δ} 1/cc h
  flat/h : ∀ {h Δ preds} →
    SECtcMaxH {Δ} (flat/cc preds) h
  _*/h_ : ∀ {h Δ τ₁ τ₂ cκ₁ cκ₂} →
    SECtcMaxH cκ₁ h →
    SECtcMaxH cκ₂ h →
    SECtcMaxH {Δ} {τ₁ `* τ₂} (cκ₁ */cc cκ₂) (suc h)
  _+/h_ : ∀ {h Δ τ₁ τ₂ cκ₁ cκ₂} →
    SECtcMaxH cκ₁ h →
    SECtcMaxH cκ₂ h →
    SECtcMaxH {Δ} {τ₁ `+ τ₂} (cκ₁ +/cc cκ₂) (suc h)
  box/h : ∀ {h Δ τ cκ} →
    SECtcMaxH cκ h →
    SECtcMaxH {Δ} {Box τ} (box/cc cκ) (suc h)
  _→/h_ : ∀ {h Δ τₐ τᵣ cκₐ cκᵣ} →
    SECtcMaxH cκₐ h →
    SECtcMaxH cκᵣ h →
    SECtcMaxH {Δ} {τₐ `→ τᵣ} (cκₐ →/cc cκᵣ) (suc h)
  μ/h_ : ∀ {h Δ τ cκ} →
    SECtcMaxH cκ h →
    SECtcMaxH {Δ} {μ τ} (μ/cc cκ) (suc h)

cmh-Σ-*₁ : ∀ {h Δ τ₁ τ₂ cκ} →
  SECtcMaxH {Δ} {τ₁ `* τ₂} cκ h →
  ∃ λ h′ → h ≡ suc h′ × SECtcMaxH (*/cc-cκ₁ cκ) h′
cmh-Σ-*₁ (cmh₁ */h cmh₂) = _ , refl ,′ cmh₁

cmh-Σ-*₂ : ∀ {h Δ τ₁ τ₂ cκ} →
  SECtcMaxH {Δ} {τ₁ `* τ₂} cκ h →
  ∃ λ h′ → h ≡ suc h′ × SECtcMaxH (*/cc-cκ₂ cκ) h′
cmh-Σ-*₂ (cmh₁ */h cmh₂) = _ , refl ,′ cmh₂

cmh-Σ-+₁ : ∀ {h Δ τ₁ τ₂ cκ} →
  SECtcMaxH {Δ} {τ₁ `+ τ₂} cκ h →
  ∃ λ h′ → h ≡ suc h′ × SECtcMaxH (+/cc-cκ₁ cκ) h′
cmh-Σ-+₁ (cmh₁ +/h cmh₂) = _ , refl ,′ cmh₁

cmh-Σ-+₂ : ∀ {h Δ τ₁ τ₂ cκ} →
  SECtcMaxH {Δ} {τ₁ `+ τ₂} cκ h →
  ∃ λ h′ → h ≡ suc h′ × SECtcMaxH (+/cc-cκ₂ cκ) h′
cmh-Σ-+₂ (cmh₁ +/h cmh₂) = _ , refl ,′ cmh₂

cmh-Σ-box : ∀ {h Δ τ cκ} →
  SECtcMaxH {Δ} {Box τ} cκ h →
  ∃ λ h′ → h ≡ suc h′ × SECtcMaxH (box/cc-cκ cκ) h′
cmh-Σ-box (box/h cmh) = _ , refl ,′ cmh

cmh-Σ-dom : ∀ {h Δ τₐ τᵣ cκ} →
  SECtcMaxH {Δ} {τₐ `→ τᵣ} cκ h →
  ∃ λ h′ → h ≡ suc h′ × SECtcMaxH (→/cc-dom-cκ cκ) h′
cmh-Σ-dom (cmhₐ →/h cmhᵣ) = _ , refl ,′ cmhₐ

cmh-Σ-rng : ∀ {h Δ τₐ τᵣ cκ} →
  SECtcMaxH {Δ} {τₐ `→ τᵣ} cκ h →
  ∃ λ h′ → h ≡ suc h′ × SECtcMaxH (→/cc-rng-cκ cκ) h′
cmh-Σ-rng (cmhₐ →/h cmhᵣ) = _ , refl ,′ cmhᵣ

cmh-Σ-μ′ : ∀ {h Δ τ cκ} →
  SECtcMaxH {Δ} {μ τ} cκ h →
  ∃ λ h′ → h ≡ suc h′ × SECtcMaxH (μ/cc-cκ′ cκ) h′
cmh-Σ-μ′ (μ/h cmh) = _ , refl ,′ cmh

cmh-pred-*₁ : ∀ {h Δ τ₁ τ₂ cκ} →
  SECtcMaxH {Δ} {τ₁ `* τ₂} cκ h →
  SECtcMaxH (*/cc-cκ₁ cκ) (pred h)
cmh-pred-*₁ cmh with _ , refl , cmh₁ ← cmh-Σ-*₁ cmh = cmh₁

cmh-pred-*₂ : ∀ {h Δ τ₁ τ₂ cκ} →
  SECtcMaxH {Δ} {τ₁ `* τ₂} cκ h →
  SECtcMaxH (*/cc-cκ₂ cκ) (pred h)
cmh-pred-*₂ cmh with _ , refl , cmh₂ ← cmh-Σ-*₂ cmh = cmh₂

cmh-pred-+₁ : ∀ {h Δ τ₁ τ₂ cκ} →
  SECtcMaxH {Δ} {τ₁ `+ τ₂} cκ h →
  SECtcMaxH (+/cc-cκ₁ cκ) (pred h)
cmh-pred-+₁ cmh with _ , refl , cmh₁ ← cmh-Σ-+₁ cmh = cmh₁

cmh-pred-+₂ : ∀ {h Δ τ₁ τ₂ cκ} →
  SECtcMaxH {Δ} {τ₁ `+ τ₂} cκ h →
  SECtcMaxH (+/cc-cκ₂ cκ) (pred h)
cmh-pred-+₂ cmh with _ , refl , cmh₂ ← cmh-Σ-+₂ cmh = cmh₂

cmh-pred-box : ∀ {h Δ τ cκ} →
  SECtcMaxH {Δ} {Box τ} cκ h →
  SECtcMaxH (box/cc-cκ cκ) (pred h)
cmh-pred-box cmh with _ , refl , cmh′ ← cmh-Σ-box cmh = cmh′

cmh-pred-dom : ∀ {h Δ τₐ τᵣ cκ} →
  SECtcMaxH {Δ} {τₐ `→ τᵣ} cκ h →
  SECtcMaxH (→/cc-dom-cκ cκ) (pred h)
cmh-pred-dom cmh with _ , refl , cmhₐ ← cmh-Σ-dom cmh = cmhₐ

cmh-pred-rng : ∀ {h Δ τₐ τᵣ cκ} →
  SECtcMaxH {Δ} {τₐ `→ τᵣ} cκ h →
  SECtcMaxH (→/cc-rng-cκ cκ) (pred h)
cmh-pred-rng cmh with _ , refl , cmhᵣ ← cmh-Σ-rng cmh = cmhᵣ

cmh-pred-μ′ : ∀ {h Δ τ cκ} →
  SECtcMaxH {Δ} {μ τ} cκ h →
  SECtcMaxH (μ/cc-cκ′ cκ) (pred h)
cmh-pred-μ′ cmh with _ , refl , cmh′ ← cmh-Σ-μ′ cmh = cmh′

cmh-weaken : ∀ {h h′ Δ τ cκ} → h ≤ h′ → SECtcMaxH {Δ} {τ} cκ h → SECtcMaxH cκ h′
cmh-weaken h≤h′       (` a)           = ` a
cmh-weaken h≤h′       1/h             = 1/h
cmh-weaken h≤h′       flat/h          = flat/h
cmh-weaken (s≤s h≤h′) (cκh₁ */h cκh₂) = (cmh-weaken h≤h′ cκh₁) */h (cmh-weaken h≤h′ cκh₂)
cmh-weaken (s≤s h≤h′) (cκh₁ +/h cκh₂) = (cmh-weaken h≤h′ cκh₁) +/h (cmh-weaken h≤h′ cκh₂)
cmh-weaken (s≤s h≤h′) (box/h cκh)     = box/h (cmh-weaken h≤h′ cκh)
cmh-weaken (s≤s h≤h′) (cκhₐ →/h cκhᵣ) = (cmh-weaken h≤h′ cκhₐ) →/h (cmh-weaken h≤h′ cκhᵣ)
cmh-weaken (s≤s h≤h′) (μ/h cκh)       = μ/h (cmh-weaken h≤h′ cκh)

cmh-weaken-suc : ∀ {h h′ Δ τ cκ} → h ≡ suc h′ → SECtcMaxH {Δ} {τ} cκ h′ → SECtcMaxH {Δ} {τ} cκ h
cmh-weaken-suc h≡1+h′ = cmh-weaken (Nat.<⇒≤ (Nat.≤-reflexive (sym h≡1+h′)))

cmh-*₁ : ∀ {h Δ τ₁ τ₂ cκ} →
  SECtcMaxH {Δ} {τ₁ `* τ₂} cκ h →
  SECtcMaxH (*/cc-cκ₁ cκ) h
cmh-*₁ cmh = Product.uncurry cmh-weaken-suc (proj₂ (cmh-Σ-*₁ cmh))

cmh-*₂ : ∀ {h Δ τ₁ τ₂ cκ} →
  SECtcMaxH {Δ} {τ₁ `* τ₂} cκ h →
  SECtcMaxH (*/cc-cκ₂ cκ) h
cmh-*₂ cmh = Product.uncurry cmh-weaken-suc (proj₂ (cmh-Σ-*₂ cmh))

cmh-+₁ : ∀ {h Δ τ₁ τ₂ cκ} →
  SECtcMaxH {Δ} {τ₁ `+ τ₂} cκ h →
  SECtcMaxH (+/cc-cκ₁ cκ) h
cmh-+₁ cmh = Product.uncurry cmh-weaken-suc (proj₂ (cmh-Σ-+₁ cmh))

cmh-+₂ : ∀ {h Δ τ₁ τ₂ cκ} →
  SECtcMaxH {Δ} {τ₁ `+ τ₂} cκ h →
  SECtcMaxH (+/cc-cκ₂ cκ) h
cmh-+₂ cmh = Product.uncurry cmh-weaken-suc (proj₂ (cmh-Σ-+₂ cmh))

cmh-box : ∀ {h Δ τ cκ} →
  SECtcMaxH {Δ} {Box τ} cκ h →
  SECtcMaxH (box/cc-cκ cκ) h
cmh-box cmh = Product.uncurry cmh-weaken-suc (proj₂ (cmh-Σ-box cmh))

cmh-dom : ∀ {h Δ τₐ τᵣ cκ} →
  SECtcMaxH {Δ} {τₐ `→ τᵣ} cκ h →
  SECtcMaxH (→/cc-dom-cκ cκ) h
cmh-dom cmh = Product.uncurry cmh-weaken-suc (proj₂ (cmh-Σ-dom cmh))

cmh-rng : ∀ {h Δ τₐ τᵣ cκ} →
  SECtcMaxH {Δ} {τₐ `→ τᵣ} cκ h →
  SECtcMaxH (→/cc-rng-cκ cκ) h
cmh-rng cmh = Product.uncurry cmh-weaken-suc (proj₂ (cmh-Σ-rng cmh))

cmh-μ′ : ∀ {h Δ τ cκ} →
  SECtcMaxH {Δ} {μ τ} cκ h →
  SECtcMaxH (μ/cc-cκ′ cκ) h
cmh-μ′ cmh = Product.uncurry cmh-weaken-suc (proj₂ (cmh-Σ-μ′ cmh))

sectc-height : ∀ {Δ τ} → SECtcN Δ τ → ℕ
sectc-height (` a)           = 0
sectc-height 1/cc            = 0
sectc-height (flat/cc preds) = 0
sectc-height (cκ₁ */cc cκ₂)  = suc (sectc-height cκ₁ ⊔ sectc-height cκ₂)
sectc-height (cκ₁ +/cc cκ₂)  = suc (sectc-height cκ₁ ⊔ sectc-height cκ₂)
sectc-height (box/cc cκ)     = suc (sectc-height cκ)
sectc-height (cκₐ →/cc cκᵣ)  = suc (sectc-height cκₐ ⊔ sectc-height cκᵣ)
sectc-height (μ/cc cκ)       = suc (sectc-height cκ)

sectc→cmh : ∀ {Δ τ} cκ → SECtcMaxH {Δ} {τ} cκ (sectc-height cκ)
sectc→cmh (` a)           = ` a
sectc→cmh 1/cc            = 1/h
sectc→cmh (flat/cc preds) = flat/h
sectc→cmh (cκ₁ */cc cκ₂)  =
  (cmh-weaken (Nat.m≤m⊔n _ _) (sectc→cmh cκ₁)) */h (cmh-weaken (Nat.m≤n⊔m _ _) (sectc→cmh cκ₂))
sectc→cmh (cκ₁ +/cc cκ₂)  =
  (cmh-weaken (Nat.m≤m⊔n _ _) (sectc→cmh cκ₁)) +/h (cmh-weaken (Nat.m≤n⊔m _ _) (sectc→cmh cκ₂))
sectc→cmh (box/cc cκ)     =
  box/h (sectc→cmh cκ)
sectc→cmh (cκₐ →/cc cκᵣ)  =
  (cmh-weaken (Nat.m≤m⊔n _ _) (sectc→cmh cκₐ)) →/h (cmh-weaken (Nat.m≤n⊔m _ _) (sectc→cmh cκᵣ))
sectc→cmh (μ/cc cκ)       =
  μ/h (sectc→cmh cκ)

cmh-height : ∀ {h Δ τ cκ} → SECtcMaxH {Δ} {τ} cκ h → sectc-height cκ ≤ h
cmh-height (` a)             = z≤n
cmh-height 1/h               = z≤n
cmh-height flat/h            = z≤n
cmh-height (cmh₁ */h cmh₂)   = s≤s (Nat.⊔-lub (cmh-height cmh₁) (cmh-height cmh₂))
cmh-height (cmh₁ +/h cmh₂)   = s≤s (Nat.⊔-lub (cmh-height cmh₁) (cmh-height cmh₂))
cmh-height (box/h cmh)       = s≤s (cmh-height cmh)
cmh-height (cmhₐ →/h cmhᵣ)   = s≤s (Nat.⊔-lub (cmh-height cmhₐ) (cmh-height cmhᵣ))
cmh-height (μ/h cmh)         = s≤s (cmh-height cmh)
