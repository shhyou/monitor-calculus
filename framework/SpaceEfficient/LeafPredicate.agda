{-# OPTIONS --safe --without-K #-}

open import Annotation.Language

module SpaceEfficient.LeafPredicate (Label : Set) (𝒜 : AnnTerm) where

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; trans; cong; subst)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)

open import Data.List.Base as List using (List; []; _∷_; map)
import Data.List.Properties as List
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (id; const)

open import Data.Tick using (Tick; evalTick; ✓_)

open import Syntax.Type
open import Syntax.Term

open import Contract.Common Label
open import Contract.Base Label 𝒜
  using ( SCtc1N; SCtc1; flat; flat-pred
        ; sκflat-change-variable; flat-pred-change-variable; checkNatSCtcs)
open import SpaceEfficient.Base Label 𝒜
open import SpaceEfficient.OrderedPredicate Label 𝒜
open AnnTerm 𝒜 hiding (State)

private variable
  Δ Δ′ : TCtxt
  τ τ₁ τ₂ τₐ τᵣ : TyN Δ
  P Q : List Pred → Set

data SECtcPreds (P : List Pred → Set) : ∀ {Δ τ} → SECtcN Δ τ → Set where
  `_ : (a : tt ∈ Δ) → SECtcPreds P (` a)
  1/ps : SECtcPreds P {Δ} 1/cc
  flat/ps : ∀ {preds} →
    (pf : P (map flat-pred preds)) →
    SECtcPreds P {Δ} (flat/cc preds)
  _*/ps_ : ∀ {cκ₁ cκ₂} →
    SECtcPreds P cκ₁ →
    SECtcPreds P cκ₂ →
    SECtcPreds P {Δ} {τ₁ `* τ₂} (cκ₁ */cc cκ₂)
  _+/ps_ : ∀ {cκ₁ cκ₂} →
    SECtcPreds P cκ₁ →
    SECtcPreds P cκ₂ →
    SECtcPreds P {Δ} {τ₁ `+ τ₂} (cκ₁ +/cc cκ₂)
  box/ps : ∀ {cκ} →
    SECtcPreds P cκ →
    SECtcPreds P {Δ} {Box τ} (box/cc cκ)
  _→/ps_ : ∀ {cκₐ cκᵣ} →
    SECtcPreds P cκₐ →
    SECtcPreds P cκᵣ →
    SECtcPreds P {Δ} {τₐ `→ τᵣ} (cκₐ →/cc cκᵣ)
  μ/ps_ : ∀ {cκ} →
    SECtcPreds P cκ →
    SECtcPreds P {Δ} {μ τ} (μ/cc cκ)

cpsrename :
  {cκ : SECtcN Δ τ} →
  SECtcPreds P cκ →
  (ren : (a : tt ∈ Δ) → tt ∈ Δ′) →
  SECtcPreds P (cκrename cκ ren)
cpsrename (` a)            ren = ` ren a
cpsrename 1/ps             ren = 1/ps
cpsrename {Δ = Δ} {Δ′ = Δ′} (flat/ps {preds = preds} pf) ren
  rewrite List.map-cong (flat-pred-change-variable {Δ} {Δ′}) preds
        | List.map-∘ {g = flat-pred} {sκflat-change-variable {Δ} {Δ′}} preds
  = flat/ps pf
cpsrename (cps₁ */ps cps₂) ren = cpsrename cps₁ ren */ps cpsrename cps₂ ren
cpsrename (cps₁ +/ps cps₂) ren = cpsrename cps₁ ren +/ps cpsrename cps₂ ren
cpsrename (box/ps cps)     ren = box/ps (cpsrename cps ren)
cpsrename (cpsₐ →/ps cpsᵣ) ren = cpsrename cpsₐ ren →/ps cpsrename cpsᵣ ren
cpsrename (μ/ps cps)       ren = μ/ps cpsrename cps (pext ren)

cpsext :
  {σ : tt ∈ Δ → TyN Δ′} →
  {σκ : (a : tt ∈ Δ) → SECtcN Δ′ (σ a)} →
  ((a : tt ∈ Δ) → SECtcPreds P (σκ a)) →
  ((a : tt ∈ (tt ∷ Δ)) → SECtcPreds P (cκext σκ a))
cpsext σps (here refl) = ` here refl
cpsext σps (there x∈Δ) = cpsrename (σps x∈Δ) there

cpssubst :
  {σ : tt ∈ Δ → TyN Δ′} →
  {σκ : (a : tt ∈ Δ) → SECtcN Δ′ (σ a)} →
  {cκ : SECtcN Δ τ} →
  SECtcPreds P cκ →
  ((a : tt ∈ Δ) → SECtcPreds P (σκ a)) →
  SECtcPreds P (cκsubst cκ σκ)
cpssubst (` a)            σps = σps a
cpssubst 1/ps             σps = 1/ps
cpssubst {Δ = Δ} {Δ′} (flat/ps {preds = preds} pf) σps
  rewrite List.map-cong (flat-pred-change-variable {Δ} {Δ′}) preds
        | List.map-∘ {g = flat-pred} {sκflat-change-variable {Δ} {Δ′}} preds
  = flat/ps pf
cpssubst (cps₁ */ps cps₂) σps = cpssubst cps₁ σps */ps cpssubst cps₂ σps
cpssubst (cps₁ +/ps cps₂) σps = cpssubst cps₁ σps +/ps cpssubst cps₂ σps
cpssubst (box/ps cps)     σps = box/ps (cpssubst cps σps)
cpssubst (cpsₐ →/ps cpsᵣ) σps = cpssubst cpsₐ σps →/ps cpssubst cpsᵣ σps
cpssubst (μ/ps cps)       σps = μ/ps (cpssubst cps (cpsext σps))

cps0mapsto [cps0↦_] : ∀ {cκ} →
  SECtcPreds P {Δ} {τ} cκ → (a : tt ∈ (tt ∷ Δ)) → SECtcPreds P ([cκ0↦ cκ ] a)
cps0mapsto cps (here refl) = cps
cps0mapsto cps (there x∈Δ) = ` x∈Δ

[cps0↦_] = cps0mapsto

cps-flat-preds : ∀ {cκ} → SECtcPreds P {Δ} cκ → P (map flat-pred (flat/cc-preds cκ))
cps-flat-preds (flat/ps pf) = pf

cps-*₁ : ∀ {cκ} →
  SECtcPreds P {Δ} {τ₁ `* τ₂} cκ → SECtcPreds P (*/cc-cκ₁ cκ)
cps-*₁ (cps₁ */ps cps₂) = cps₁

cps-*₂ : ∀ {cκ} →
  SECtcPreds P {Δ} {τ₁ `* τ₂} cκ → SECtcPreds P (*/cc-cκ₂ cκ)
cps-*₂ (cps₁ */ps cps₂) = cps₂

cps-+₁ : ∀ {cκ} →
  SECtcPreds P {Δ} {τ₁ `+ τ₂} cκ → SECtcPreds P (+/cc-cκ₁ cκ)
cps-+₁ (cps₁ +/ps cps₂) = cps₁

cps-+₂ : ∀ {cκ} →
  SECtcPreds P {Δ} {τ₁ `+ τ₂} cκ → SECtcPreds P (+/cc-cκ₂ cκ)
cps-+₂ (cps₁ +/ps cps₂) = cps₂

cps-box : ∀ {cκ} →
  SECtcPreds P {Δ} {Box τ} cκ → SECtcPreds P (box/cc-cκ cκ)
cps-box (box/ps cps) = cps

cps-dom : ∀ {cκ} →
  SECtcPreds P {Δ} {τₐ `→ τᵣ} cκ → SECtcPreds P (→/cc-dom-cκ cκ)
cps-dom (cpsₐ →/ps cpsᵣ) = cpsₐ

cps-rng : ∀ {cκ} →
  SECtcPreds P {Δ} {τₐ `→ τᵣ} cκ → SECtcPreds P (→/cc-rng-cκ cκ)
cps-rng (cpsₐ →/ps cpsᵣ) = cpsᵣ

cps-μ : ∀ {cκ} →
  SECtcPreds P {Δ} {μ τ} cκ → SECtcPreds P (μ/cc-cκ cκ)
cps-μ (μ/ps cps) = cpssubst cps [cps0↦ μ/ps cps ]

cps-μ′ : ∀ {cκ} →
  SECtcPreds P {Δ} {μ τ} cκ → SECtcPreds P (μ/cc-cκ′ cκ)
cps-μ′ (μ/ps cps) = cps

module _ (𝒜view : AnnTermView 𝒜 𝒜cctc) (stronger? : Pred → Pred → Dec ⊤) where
  open SECtcTransitSteps 𝒜view stronger?

  cps-join : ∀ {cκ′ cκ} →
    (pjoin-flats : ∀ {Δ} preds {preds′} →
      P (map flat-pred preds) →
      P (map flat-pred preds′) →
      P (map flat-pred (evalTick (✓ join-flats {Δ} preds preds′)))) →
    SECtcPreds P cκ′ →
    SECtcPreds P cκ →
    SECtcPreds P {Δ} {τ} (evalTick (✓ join cκ′ cκ))
  cps-join pjoin-flats (` a)            (` .a)             = ` a
  cps-join pjoin-flats 1/ps             1/ps               = 1/ps
  cps-join pjoin-flats (flat/ps pf)     (flat/ps pf′)      = flat/ps (pjoin-flats _ pf pf′)
  cps-join pjoin-flats (cps₁ */ps cps₂) (cps₁′ */ps cps₂′) =
    (cps-join pjoin-flats cps₁ cps₁′) */ps (cps-join pjoin-flats cps₂ cps₂′)
  cps-join pjoin-flats (cps₁ +/ps cps₂) (cps₁′ +/ps cps₂′) =
    (cps-join pjoin-flats cps₁ cps₁′) +/ps (cps-join pjoin-flats cps₂ cps₂′)
  cps-join pjoin-flats (box/ps cps)     (box/ps cps′)      = box/ps (cps-join pjoin-flats cps cps′)
  cps-join pjoin-flats (cpsₐ →/ps cpsᵣ) (cpsₐ′ →/ps cpsᵣ′) =
    (cps-join pjoin-flats cpsₐ′ cpsₐ) →/ps (cps-join pjoin-flats cpsᵣ cpsᵣ′)
  cps-join pjoin-flats (μ/ps cps)       (μ/ps cps′)        = μ/ps (cps-join pjoin-flats cps cps′)

cps-map : ∀ {cκ} →
  (∀ {Δ preds} → P (map (flat-pred {Δ = Δ}) preds) → Q (map flat-pred preds)) →
  SECtcPreds P {Δ} {τ} cκ → SECtcPreds Q cκ
cps-map P⇒Q (` a)            = ` a
cps-map P⇒Q 1/ps             = 1/ps
cps-map P⇒Q (flat/ps pf)     = flat/ps (P⇒Q pf)
cps-map P⇒Q (cps₁ */ps cps₂) = (cps-map P⇒Q cps₁) */ps (cps-map P⇒Q cps₂)
cps-map P⇒Q (cps₁ +/ps cps₂) = (cps-map P⇒Q cps₁) +/ps (cps-map P⇒Q cps₂)
cps-map P⇒Q (box/ps cps)     = box/ps (cps-map P⇒Q cps)
cps-map P⇒Q (cpsₐ →/ps cpsᵣ) = (cps-map P⇒Q cpsₐ) →/ps (cps-map P⇒Q cpsᵣ)
cps-map P⇒Q (μ/ps cps)       = μ/ps (cps-map P⇒Q cps)
