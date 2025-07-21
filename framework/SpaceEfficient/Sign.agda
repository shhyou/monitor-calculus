{-# OPTIONS --without-K --safe #-}

open import Annotation.Language

module SpaceEfficient.Sign (Label : Set) (𝒜 : AnnTerm) where

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; subst; trans; cong)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as ListAll
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (const)

open import Data.Tick using (Tick; evalTick; ✓_)

open import Syntax.Type

open import Contract.Common Label
open import SpaceEfficient.Base Label 𝒜
open import SpaceEfficient.OrderedPredicate Label 𝒜

private variable
  Δ Δ′ : TCtxt
  τ τ₁ τ₂ τₐ τᵣ : TyN Δ
  ± : Sgn
  δ : All (const Sgn) Δ
  δ′ : All (const Sgn) Δ′

data SECtcSigned : ∀ {Δ τ} → (± : Sgn) → (δ : All (const Sgn) Δ) → (cκ : SECtcN Δ τ) → Set where
  var/p : ∀ a →
    ± ≡ ListAll.lookup δ a →
    SECtcSigned {Δ} ± δ (` a)
  1/p :
    SECtcSigned {Δ} ± δ 1/cc
  flat/p : ∀ {preds} →
    SECtcSigned {Δ} ± δ (flat/cc preds)
  _*/p_ : ∀ {cκ₁ cκ₂} →
    SECtcSigned                ± δ cκ₁ →
    SECtcSigned                ± δ cκ₂ →
    SECtcSigned {Δ} {τ₁ `* τ₂} ± δ (cκ₁ */cc cκ₂)
  _+/p_ : ∀ {cκ₁ cκ₂} →
    SECtcSigned                ± δ cκ₁ →
    SECtcSigned                ± δ cκ₂ →
    SECtcSigned {Δ} {τ₁ `+ τ₂} ± δ (cκ₁ +/cc cκ₂)
  box/p : ∀ {cκ} →
    SECtcSigned             ± δ cκ →
    SECtcSigned {Δ} {Box τ} ± δ (box/cc cκ)
  _→/p_ : ∀ {cκₐ cκᵣ} →
    SECtcSigned                (negate ±) δ cκₐ →
    SECtcSigned                ±          δ cκᵣ →
    SECtcSigned {Δ} {τₐ `→ τᵣ} ±          δ (cκₐ →/cc cκᵣ)
  μ/p_ : ∀ {cκ} →
    SECtcSigned           ± (± ∷ δ) cκ →
    SECtcSigned {Δ} {μ τ} ± δ       (μ/cc cκ)

pmκnegate : ∀ {cκ} →
  SECtcSigned ± δ cκ →
  SECtcSigned {Δ} {τ} (negate ±) (ListAll.map negate δ) cκ
pmκnegate {δ = δ} (var/p a eq) = var/p a (trans (cong negate eq) (sym (ListAll.lookup-map δ a)))
pmκnegate 1/p             = 1/p
pmκnegate flat/p          = flat/p
pmκnegate (pmκ₁ */p pmκ₂) = pmκnegate pmκ₁ */p pmκnegate pmκ₂
pmκnegate (pmκ₁ +/p pmκ₂) = pmκnegate pmκ₁ +/p pmκnegate pmκ₂
pmκnegate (box/p pmκ)     = box/p (pmκnegate pmκ)
pmκnegate (pmκₐ →/p pmκᵣ) = pmκnegate pmκₐ →/p pmκnegate pmκᵣ
pmκnegate (μ/p pmκ)       = μ/p (pmκnegate pmκ)

δrenext :
  {ren : tt ∈ Δ → tt ∈ Δ′} →
  (δren : (a : tt ∈ Δ) → ListAll.lookup δ a ≡ ListAll.lookup δ′ (ren a)) →
  (a : tt ∈ (tt ∷ Δ)) → ListAll.lookup (± ∷ δ) a ≡ ListAll.lookup (± ∷ δ′) (pext ren a)
δrenext δren (here refl) = refl
δrenext δren (there a∈Δ) = δren a∈Δ

pmκrename :
  {cκ : SECtcN Δ τ} →
  SECtcSigned ± δ cκ →
  {ren : tt ∈ Δ → tt ∈ Δ′} →
  (δren : ∀ a → ListAll.lookup δ a ≡ ListAll.lookup δ′ (ren a)) →
  SECtcSigned ± δ′ (cκrename cκ ren)
pmκrename (var/p a eq) {ren} δren rewrite δren a = var/p (ren a) eq
pmκrename 1/p             δren = 1/p
pmκrename flat/p          δren = flat/p
pmκrename (pmκ₁ */p pmκ₂) δren = pmκrename pmκ₁ δren */p pmκrename pmκ₂ δren
pmκrename (pmκ₁ +/p pmκ₂) δren = pmκrename pmκ₁ δren +/p pmκrename pmκ₂ δren
pmκrename (box/p pmκ)     δren = box/p (pmκrename pmκ δren)
pmκrename (pmκₐ →/p pmκᵣ) δren = pmκrename pmκₐ δren →/p pmκrename pmκᵣ δren
pmκrename (μ/p pmκ)       δren = μ/p (pmκrename pmκ (δrenext δren))

pmκext :
  {σ : tt ∈ Δ → TyN Δ′} →
  {σκ : (a : tt ∈ Δ) → SECtcN Δ′ (σ a)} →
  (σp : (a : tt ∈ Δ) → SECtcSigned (ListAll.lookup δ a) δ′ (σκ a)) →
  (a : tt ∈ (tt ∷ Δ)) → SECtcSigned {tt ∷ Δ′} (ListAll.lookup (± ∷ δ) a) (± ∷ δ′) (cκext σκ a)
pmκext σp (here refl) = var/p (here refl) refl
pmκext σp (there x∈Δ) = pmκrename (σp x∈Δ) (λ a → refl)

pmκsubst :
  {σ : tt ∈ Δ → TyN Δ′} →
  {σκ : (a : tt ∈ Δ) → SECtcN Δ′ (σ a)} →
  {cκ : SECtcN Δ τ} →
  SECtcSigned ± δ cκ →
  (σp : (a : tt ∈ Δ) → SECtcSigned (ListAll.lookup δ a) δ′ (σκ a)) →
  SECtcSigned ± δ′ (cκsubst cκ σκ)
pmκsubst (var/p a eq)    σp rewrite eq = σp a
pmκsubst 1/p             σp = 1/p
pmκsubst flat/p          σp = flat/p
pmκsubst (pmκ₁ */p pmκ₂) σp = pmκsubst pmκ₁ σp */p pmκsubst pmκ₂ σp
pmκsubst (pmκ₁ +/p pmκ₂) σp = pmκsubst pmκ₁ σp +/p pmκsubst pmκ₂ σp
pmκsubst (box/p pmκ)     σp = box/p (pmκsubst pmκ σp)
pmκsubst (pmκₐ →/p pmκᵣ) σp = pmκsubst pmκₐ σp →/p pmκsubst pmκᵣ σp
pmκsubst (μ/p pmκ)       σp = μ/p (pmκsubst pmκ (pmκext σp))

pmκ0mapsto [pmκ0↦_] : {cκ : SECtcN Δ τ} →
  SECtcSigned {Δ} ± δ cκ →
  (a : tt ∈ (tt ∷ Δ)) →
  SECtcSigned {Δ} (ListAll.lookup (± ∷ δ) a) δ ([cκ0↦ cκ ] a)
pmκ0mapsto pmκ (here refl) = pmκ
pmκ0mapsto pmκ (there x∈Δ) = var/p x∈Δ refl

[pmκ0↦_] = pmκ0mapsto

pmκ-*₁ : ∀ {cκ} →
  SECtcSigned {Δ} {τ₁ `* τ₂} ± δ cκ → SECtcSigned ± δ (*/cc-cκ₁ cκ)
pmκ-*₁ (pmκ₁ */p pmκ₂) = pmκ₁

pmκ-*₂ : ∀ {cκ} →
  SECtcSigned {Δ} {τ₁ `* τ₂} ± δ cκ → SECtcSigned ± δ (*/cc-cκ₂ cκ)
pmκ-*₂ (pmκ₁ */p pmκ₂) = pmκ₂

pmκ-+₁ : ∀ {cκ} →
  SECtcSigned {Δ} {τ₁ `+ τ₂} ± δ cκ → SECtcSigned ± δ (+/cc-cκ₁ cκ)
pmκ-+₁ (pmκ₁ +/p pmκ₂) = pmκ₁

pmκ-+₂ : ∀ {cκ} →
  SECtcSigned {Δ} {τ₁ `+ τ₂} ± δ cκ → SECtcSigned ± δ (+/cc-cκ₂ cκ)
pmκ-+₂ (pmκ₁ +/p pmκ₂) = pmκ₂

pmκ-box : ∀ {cκ} →
  SECtcSigned {Δ} {Box τ} ± δ cκ → SECtcSigned ± δ (box/cc-cκ cκ)
pmκ-box (box/p pmκ) = pmκ

pmκ-dom : ∀ {cκ} →
  SECtcSigned {Δ} {τₐ `→ τᵣ} ± δ cκ → SECtcSigned (negate ±) δ (→/cc-dom-cκ cκ)
pmκ-dom (pmκₐ →/p pmκᵣ) = pmκₐ

pmκ-rng : ∀ {cκ} →
  SECtcSigned {Δ} {τₐ `→ τᵣ} ± δ cκ → SECtcSigned ± δ (→/cc-rng-cκ cκ)
pmκ-rng (pmκₐ →/p pmκᵣ) = pmκᵣ

pmκ-μ : ∀ {cκ} →
  SECtcSigned {Δ} {μ τ} ± δ cκ →
  SECtcSigned ± δ (μ/cc-cκ cκ)
pmκ-μ (μ/p pmκ) = pmκsubst pmκ [pmκ0↦ μ/p pmκ ]

module _ (𝒜cctc-view : AnnTermView 𝒜 𝒜cctc) (stronger? : Pred → Pred → Dec ⊤) where
  open SECtcTransitSteps 𝒜cctc-view stronger?

  pmκ-join : ∀ {cκ cκ′} →
    SECtcSigned ± δ cκ →
    SECtcSigned ± δ cκ′ →
    SECtcSigned {Δ} {τ} ± δ (evalTick (✓ join cκ cκ′))
  pmκ-join (var/p a lookup-eq)  (var/p .a lookup-eq′)   = var/p a lookup-eq
  pmκ-join 1/p                  1/p                     = 1/p
  pmκ-join flat/p               flat/p                  = flat/p
  pmκ-join (pmκ₁ */p pmκ₂)      (pmκ₁′ */p pmκ₂′)       = (pmκ-join pmκ₁ pmκ₁′) */p (pmκ-join pmκ₂ pmκ₂′)
  pmκ-join (pmκ₁ +/p pmκ₂)      (pmκ₁′ +/p pmκ₂′)       = (pmκ-join pmκ₁ pmκ₁′) +/p (pmκ-join pmκ₂ pmκ₂′)
  pmκ-join (box/p pmκ)          (box/p pmκ′)            = box/p (pmκ-join pmκ pmκ′)
  pmκ-join (pmκₐ →/p pmκᵣ)      (pmκₐ′ →/p pmκᵣ′)       = (pmκ-join pmκₐ′ pmκₐ) →/p (pmκ-join pmκᵣ pmκᵣ′)
  pmκ-join (μ/p pmκ)            (μ/p pmκ′)              = μ/p (pmκ-join pmκ pmκ′)
