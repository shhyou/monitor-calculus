{-# OPTIONS --without-K --safe #-}

open import Annotation.Language

module Blame.Sign (Label : Set) (𝒜 : AnnTerm) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; subst; trans)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as ListAll
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (const)

open import Syntax.Type

open import Contract.Common Label
open import Contract.Base Label 𝒜

private variable
  Δ Δ′ : TCtxt
  τ τ₁ τ₂ τₐ τᵣ : TyN Δ

  ± : Sgn
  δ  : All (const Sgn) Δ
  δ′ : All (const Sgn) Δ′

data SCtcSigned : ∀ {Δ τ} → (± : Sgn) → (δ : All (const Sgn) Δ) → (sκ : SCtc1N Δ τ) → Set where
  `_ : ∀ a →
    SCtcSigned {Δ} (ListAll.lookup δ a) δ (` a)
  1/p :
    SCtcSigned {Δ} ± δ 1/c
  flat/p : ∀ {l e} →
    SCtcSigned {Δ} ± δ (flat l e)
  _*/p_ : ∀ {sκ₁ sκ₂} →
    SCtcSigned                ± δ sκ₁ →
    SCtcSigned                ± δ sκ₂ →
    SCtcSigned {Δ} {τ₁ `* τ₂} ± δ (sκ₁ */c sκ₂)
  _+/p_ : ∀ {sκ₁ sκ₂} →
    SCtcSigned                ± δ sκ₁ →
    SCtcSigned                ± δ sκ₂ →
    SCtcSigned {Δ} {τ₁ `+ τ₂} ± δ (sκ₁ +/c sκ₂)
  box/p : ∀ {sκ} →
    SCtcSigned             ± δ sκ →
    SCtcSigned {Δ} {Box τ} ± δ (box/c sκ)
  _→/p_ : ∀ {sκₐ sκᵣ} →
    SCtcSigned                (negate ±) δ sκₐ →
    SCtcSigned                ±          δ sκᵣ →
    SCtcSigned {Δ} {τₐ `→ τᵣ} ±          δ (sκₐ →/c sκᵣ)
  μ/p_ : ∀ {sκ} →
    SCtcSigned           ± (± ∷ δ) sκ →
    SCtcSigned {Δ} {μ τ} ± δ       (μ/c sκ)

pmκnegate : ∀ {sκ} →
  SCtcSigned ± δ sκ →
  SCtcSigned {Δ} {τ} (negate ±) (ListAll.map negate δ) sκ
pmκnegate {δ = δ} (` a) rewrite sym (ListAll.lookup-map {f = negate} δ a) = ` a
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
δrenext δren (here refl)        = refl
δrenext δren (there a∈Δ) = δren a∈Δ

pmκrename :
  {sκ : SCtc1N Δ τ} →
  SCtcSigned ± δ sκ →
  {ren : tt ∈ Δ → tt ∈ Δ′} →
  (δren : ∀ a → ListAll.lookup δ a ≡ ListAll.lookup δ′ (ren a)) →
  SCtcSigned ± δ′ (sκrename sκ ren)
pmκrename (` a)     {ren} δren rewrite δren a = ` (ren a)
pmκrename 1/p             δren = 1/p
pmκrename flat/p          δren = flat/p
pmκrename (pmκ₁ */p pmκ₂) δren = pmκrename pmκ₁ δren */p pmκrename pmκ₂ δren
pmκrename (pmκ₁ +/p pmκ₂) δren = pmκrename pmκ₁ δren +/p pmκrename pmκ₂ δren
pmκrename (box/p pmκ)     δren = box/p (pmκrename pmκ δren)
pmκrename (pmκₐ →/p pmκᵣ) δren = pmκrename pmκₐ δren →/p pmκrename pmκᵣ δren
pmκrename (μ/p pmκ)       δren = μ/p (pmκrename pmκ (δrenext δren))

pmκext :
  {σ : tt ∈ Δ → TyN Δ′} →
  {σκ : (a : tt ∈ Δ) → SCtc1N Δ′ (σ a)} →
  (σp : (a : tt ∈ Δ) → SCtcSigned (ListAll.lookup δ a) δ′ (σκ a)) →
  (a : tt ∈ (tt ∷ Δ)) → SCtcSigned {tt ∷ Δ′} (ListAll.lookup (± ∷ δ) a) (± ∷ δ′) (sκext σκ a)
pmκext σp (here refl)        = ` (here refl)
pmκext σp (there x∈Δ) = pmκrename (σp x∈Δ) (λ a → refl)

pmκsubst :
  {σ : tt ∈ Δ → TyN Δ′} →
  {σκ : (a : tt ∈ Δ) → SCtc1N Δ′ (σ a)} →
  {sκ : SCtc1N Δ τ} →
  SCtcSigned ± δ sκ →
  (σp : (a : tt ∈ Δ) → SCtcSigned (ListAll.lookup δ a) δ′ (σκ a)) →
  SCtcSigned ± δ′ (sκsubst sκ σκ)
pmκsubst (` a)           σp = σp a
pmκsubst 1/p             σp = 1/p
pmκsubst flat/p          σp = flat/p
pmκsubst (pmκ₁ */p pmκ₂) σp = pmκsubst pmκ₁ σp */p pmκsubst pmκ₂ σp
pmκsubst (pmκ₁ +/p pmκ₂) σp = pmκsubst pmκ₁ σp +/p pmκsubst pmκ₂ σp
pmκsubst (box/p pmκ)     σp = box/p (pmκsubst pmκ σp)
pmκsubst (pmκₐ →/p pmκᵣ) σp = pmκsubst pmκₐ σp →/p pmκsubst pmκᵣ σp
pmκsubst (μ/p pmκ)       σp = μ/p (pmκsubst pmκ (pmκext σp))

pmκ0mapsto [pmκ0↦_] : {sκ : SCtc1N Δ τ} →
  SCtcSigned {Δ} ± δ sκ →
  (a : tt ∈ (tt ∷ Δ)) →
  SCtcSigned {Δ} (ListAll.lookup (± ∷ δ) a) δ ([sκ0↦ sκ ] a)
pmκ0mapsto pmκ (here refl) = pmκ
pmκ0mapsto pmκ (there x∈Δ) = ` x∈Δ

[pmκ0↦_] = pmκ0mapsto

pmκ-*₁ : ∀ {sκ} →
  SCtcSigned {Δ} {τ₁ `* τ₂} ± δ sκ → SCtcSigned ± δ (*/c-sκ₁ sκ)
pmκ-*₁ (pmκ₁ */p pmκ₂) = pmκ₁

pmκ-*₂ : ∀ {sκ} →
  SCtcSigned {Δ} {τ₁ `* τ₂} ± δ sκ → SCtcSigned ± δ (*/c-sκ₂ sκ)
pmκ-*₂ (pmκ₁ */p pmκ₂) = pmκ₂

pmκ-+₁ : ∀ {sκ} →
  SCtcSigned {Δ} {τ₁ `+ τ₂} ± δ sκ → SCtcSigned ± δ (+/c-sκ₁ sκ)
pmκ-+₁ (pmκ₁ +/p pmκ₂) = pmκ₁

pmκ-+₂ : ∀ {sκ} →
  SCtcSigned {Δ} {τ₁ `+ τ₂} ± δ sκ → SCtcSigned ± δ (+/c-sκ₂ sκ)
pmκ-+₂ (pmκ₁ +/p pmκ₂) = pmκ₂

pmκ-box : ∀ {sκ} →
  SCtcSigned {Δ} {Box τ} ± δ sκ → SCtcSigned ± δ (box/c-sκ sκ)
pmκ-box (box/p pmκ) = pmκ

pmκ-dom : ∀ {sκ} →
  SCtcSigned {Δ} {τₐ `→ τᵣ} ± δ sκ → SCtcSigned (negate ±) δ (→/c-dom-sκ sκ)
pmκ-dom (pmκₐ →/p pmκᵣ) = pmκₐ

pmκ-rng : ∀ {sκ} →
  SCtcSigned {Δ} {τₐ `→ τᵣ} ± δ sκ → SCtcSigned ± δ (→/c-rng-sκ sκ)
pmκ-rng (pmκₐ →/p pmκᵣ) = pmκᵣ

pmκ-μ : ∀ {sκ} →
  SCtcSigned {Δ} {μ τ} ± δ sκ →
  SCtcSigned ± δ (μ/c-sκ sκ)
pmκ-μ (μ/p pmκ) = pmκsubst pmκ [pmκ0↦ μ/p pmκ ]
