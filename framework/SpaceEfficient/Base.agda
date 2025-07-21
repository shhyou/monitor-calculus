{-# OPTIONS --safe --without-K #-}

open import Annotation.Language

module SpaceEfficient.Base (Label : Set) (𝒜 : AnnTerm) where

open import Relation.Nullary using (Dec; yes; no; _because_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; _++_; map; filter)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Effect.Monad using (RawMonad)

open import Data.Tick using (Tick; ✓_; monad; evalTick)

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base

open import Contract.Common Label
open import Contract.Base Label 𝒜
  using (SCtc1N; SCtc1; flat; flat-pred; sκflat-change-variable; checkNatSCtcs)
open import SpaceEfficient.OrderedPredicate Label 𝒜

open AnnTerm 𝒜 using (Ann; State)

import TransitionRelationUtil
private
  variable
    Δ Δ′ : TCtxt
    τ τ₁ τ₂ τₐ τᵣ : TyN Δ
  module TR = TransitionRelationUtil State

data SECtcN : (Δ : TCtxt) → TyN Δ → Set where
  `_      : (a : tt ∈ Δ) → SECtcN Δ (` a)
  1/cc    : SECtcN Δ `1
  flat/cc : (preds : List (SCtc1N Δ `ℕ)) → SECtcN Δ `ℕ
  _*/cc_  : SECtcN Δ τ₁ → SECtcN Δ τ₂ → SECtcN Δ (τ₁ `* τ₂)
  _+/cc_  : SECtcN Δ τ₁ → SECtcN Δ τ₂ → SECtcN Δ (τ₁ `+ τ₂)
  box/cc  : SECtcN Δ τ → SECtcN Δ (Box τ)
  _→/cc_  : SECtcN Δ τₐ → SECtcN Δ τᵣ → SECtcN Δ (τₐ `→ τᵣ)
  μ/cc_   : SECtcN (tt ∷ Δ) τ → SECtcN Δ (μ τ)

cκrename :
  SECtcN Δ τ →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  SECtcN Δ′ (trename τ ren)
cκrename (` a)            ren = ` ren a
cκrename 1/cc             ren = 1/cc
cκrename (flat/cc preds)  ren = flat/cc (map sκflat-change-variable preds)
cκrename (κ₁ */cc κ₂)     ren = cκrename κ₁ ren */cc cκrename κ₂ ren
cκrename (κ₁ +/cc κ₂)     ren = cκrename κ₁ ren +/cc cκrename κ₂ ren
cκrename (box/cc κ)       ren = box/cc (cκrename κ ren)
cκrename (κₐ →/cc κᵣ)     ren = cκrename κₐ ren →/cc cκrename κᵣ ren
cκrename (μ/cc κ)         ren = μ/cc (cκrename κ (pext ren))

cκext :
  {σ : tt ∈ Δ → TyN Δ′} →
  (σκ : (a : tt ∈ Δ) → SECtcN Δ′ (σ a)) →
  (a : tt ∈ (tt ∷ Δ)) → SECtcN (tt ∷ Δ′) (text σ a)
cκext σκ (here refl) = ` here refl
cκext σκ (there x∈Δ) = cκrename (σκ x∈Δ) there

cκsubst :
  {σ : tt ∈ Δ → TyN Δ′} →
  SECtcN Δ τ →
  (σκ : (a : tt ∈ Δ) → SECtcN Δ′ (σ a)) →
  SECtcN Δ′ (tsubst τ σ)
cκsubst (` a)            σκ = σκ a
cκsubst 1/cc             σκ = 1/cc
cκsubst (flat/cc preds)  σκ = flat/cc (map sκflat-change-variable preds)
cκsubst (κ₁ */cc κ₂)     σκ = cκsubst κ₁ σκ */cc cκsubst κ₂ σκ
cκsubst (κ₁ +/cc κ₂)     σκ = cκsubst κ₁ σκ +/cc cκsubst κ₂ σκ
cκsubst (box/cc κ)       σκ = box/cc (cκsubst κ σκ)
cκsubst (κₐ →/cc κᵣ)     σκ = cκsubst κₐ σκ →/cc cκsubst κᵣ σκ
cκsubst (μ/cc κ)         σκ = μ/cc (cκsubst κ (cκext σκ))

cκ0mapsto [cκ0↦_] : SECtcN Δ τ → (a : tt ∈ (tt ∷ Δ)) → SECtcN Δ ([t0↦ τ ] a)
cκ0mapsto κ (here refl) = κ
cκ0mapsto κ (there x∈Δ) = ` x∈Δ

[cκ0↦_] = cκ0mapsto

flat/cc-preds : SECtcN Δ `ℕ → List (SCtc1N Δ `ℕ)
flat/cc-preds (flat/cc preds) = preds

flat/cc-η : (cκ : SECtcN Δ `ℕ) → cκ ≡ flat/cc (flat/cc-preds cκ)
flat/cc-η (flat/cc preds) = refl

*/cc-cκ₁ : SECtcN Δ (τ₁ `* τ₂) → SECtcN Δ τ₁
*/cc-cκ₁ (κ₁ */cc κ₂) = κ₁

*/cc-cκ₂ : SECtcN Δ (τ₁ `* τ₂) → SECtcN Δ τ₂
*/cc-cκ₂ (κ₁ */cc κ₂) = κ₂

+/cc-cκ₁ : SECtcN Δ (τ₁ `+ τ₂) → SECtcN Δ τ₁
+/cc-cκ₁ (κ₁ +/cc κ₂) = κ₁

+/cc-cκ₂ : SECtcN Δ (τ₁ `+ τ₂) → SECtcN Δ τ₂
+/cc-cκ₂ (κ₁ +/cc κ₂) = κ₂

box/cc-cκ : SECtcN Δ (Box τ) → SECtcN Δ τ
box/cc-cκ (box/cc κ) = κ

→/cc-dom-cκ : SECtcN Δ (τₐ `→ τᵣ) → SECtcN Δ τₐ
→/cc-dom-cκ (κₐ →/cc κᵣ) = κₐ

→/cc-rng-cκ : SECtcN Δ (τₐ `→ τᵣ) → SECtcN Δ τᵣ
→/cc-rng-cκ (κₐ →/cc κᵣ) = κᵣ

μ/cc-cκ : SECtcN Δ (μ τ) → SECtcN Δ (tsubst τ [t0↦ μ τ ])
μ/cc-cκ (μ/cc κ) = cκsubst κ [cκ0↦ μ/cc κ ]

μ/cc-cκ′ : SECtcN Δ (μ τ) → SECtcN (tt ∷ Δ) τ
μ/cc-cκ′ (μ/cc κ) = κ

SECtc : Ty → Set
SECtc τ = SECtcN [] τ

𝒜cctc : AnnTerm
AnnTerm.Ann   𝒜cctc τ = SECtcN [] τ
AnnTerm.State 𝒜cctc   = Status

module SECtcTransitSteps (𝒜view : AnnTermView 𝒜 𝒜cctc) (stronger? : Pred → Pred → Dec ⊤) where
  open Agda.Primitive using (Level; lzero; lsuc)

  open AnnTermViewUtils 𝒜view
  open RawMonad {f = lzero} monad

  checkNatSECtcs :
    List (SCtc1 `ℕ) →
    (v : Ann  ∣  [] ⊢ `ℕ) →
    State → State → Set
  checkNatSECtcs [] v = TR.id
  checkNatSECtcs (flat l e ∷ sκs) v =
    ( (guardState Ok  TR.∘  CheckNatPred getState putState (∅tr ⊢_,_⟶*_,_) l e v) TR.⊎
      (λ s s′ → ∃ λ l → guardState (Err l) s s′)  ) TR.∘
    checkNatSECtcs sκs v

  fallthrough-check-nat-cctcs : ∀ {n l s} →
    getATState 𝒜view s ≡ Err l →
    (sκs : List (SCtc1N [] `ℕ)) →
    checkNatSECtcs sκs n s s
  fallthrough-check-nat-cctcs s-eq [] = refl
  fallthrough-check-nat-cctcs s-eq (flat l′ ep ∷ sκs) =
    _ , inj₂ (_ , s-eq ,′ refl) ,′ fallthrough-check-nat-cctcs s-eq sκs

  checkNatSECtc :
    SECtc `ℕ →
    (v : Ann  ∣  [] ⊢ `ℕ) →
    State → State → Set
  checkNatSECtc (flat/cc preds) v = checkNatSECtcs preds v

  drop : ∀ {Δ} → List (SCtc1N Δ `ℕ) → Ann ∣ `ℕ ∷ [] ⊢ `ℕ → Tick (List (SCtc1N Δ `ℕ))
  drop []                   e = ✓ return []
  drop (flat l e′ ∷ preds′) e = do
    b ← ✓ return (Dec.does (stronger? e e′))
    ✓ if b
        then ✓ drop preds′ e
        else do collapsedPreds ← ✓ drop preds′ e
                ✓ return (flat l e′ ∷ collapsedPreds)

  join-flats : ∀ {Δ} → List (SCtc1N Δ `ℕ) → List (SCtc1N Δ `ℕ) → Tick (List (SCtc1N Δ `ℕ))
  join-flats []                 preds′ = ✓ return preds′
  join-flats (flat l e ∷ preds) preds′ = do
    mergedPreds    ← ✓ join-flats preds preds′
    collapsedPreds ← ✓ drop mergedPreds e
    ✓ return (flat l e ∷ collapsedPreds)

  join : ∀ {Δ τ} → SECtcN Δ τ → SECtcN Δ τ → Tick (SECtcN Δ τ)
  join (` a)          (` .a)           = ✓ return (` a)
  join 1/cc           1/cc             = ✓ return 1/cc
  join (flat/cc preds) (flat/cc preds′) = do
    preds″ ← ✓ join-flats preds preds′
    ✓ return (flat/cc preds″)
  join (cκ₁ */cc cκ₂) (cκ₁′ */cc cκ₂′) = do
    cκ  ← ✓ join cκ₁ cκ₁′
    cκ′ ← ✓ join cκ₂ cκ₂′
    ✓ return (cκ */cc cκ′)
  join (cκ₁ +/cc cκ₂) (cκ₁′ +/cc cκ₂′) = do
    cκ  ← ✓ join cκ₁ cκ₁′
    cκ′ ← ✓ join cκ₂ cκ₂′
    ✓ return (cκ +/cc cκ′)
  join (box/cc cκ)    (box/cc cκ′)     = do
    cκ″ ← ✓ join cκ cκ′
    ✓ return (box/cc cκ″)
  join (cκₐ →/cc cκᵣ) (cκₐ′ →/cc cκᵣ′) = do
    cκ  ← ✓ join cκₐ′ cκₐ
    cκ′ ← ✓ join cκᵣ cκᵣ′
    ✓ return (cκ →/cc cκ′)
  join (μ/cc cκ)      (μ/cc cκ′)       = do
    cκ″ ← ✓ join cκ cκ′
    ✓ return (μ/cc cκ″)

  𝒯cctc : AnnTransit 𝒜
  𝒯cctc `R-cross-unit (_ , refl) (ϑ , tt) ψ ψ′ =
    guardState Ok
  𝒯cctc `R-cross-nat (_ , refl) (ϑ , isval) ψ ψ′ =
    guardState Ok  TR.∘
    checkNatSECtc (getAnn(ψ(here refl))) (ϑ(here refl))
  𝒯cctc `R-cross-cons (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁ , isval₂) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ cκ , cκ₁ , cκ₂ ←
                                      ψ(here refl) , ψ′(here refl) , ψ′(there (here refl)) ]
                                cκ₁ ≡ */cc-cκ₁ cκ ×
                                cκ₂ ≡ */cc-cκ₂ cκ ]
  𝒯cctc `R-cross-inl (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ cκ , cκ₁ ← ψ(here refl) , ψ′(here refl) ]
                                cκ₁ ≡ +/cc-cκ₁ cκ ]
  𝒯cctc `R-cross-inr (_ , (τ₁ , τ₂) , refl) (ϑ , isval₂) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ cκ , cκ₂ ← ψ(here refl) , ψ′(here refl) ]
                                cκ₂ ≡ +/cc-cκ₂ cκ ]
  𝒯cctc `R-cross-roll (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ cκ , cκ′ ← ψ(here refl) , ψ′(here refl) ]
                                cκ′ ≡ μ/cc-cκ cκ ]
  𝒯cctc `R-cross-box (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ cκ , cκ′ ← ψ(here refl) , ψ′(here refl) ]
                                cκ′ ≡ cκ ]
  𝒯cctc `R-cross-lam (_ , (τₐ , τᵣ) , refl) (ϑ , tt) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ cκ , cκ′ ← ψ(here refl) , ψ′(here refl) ]
                                cκ′ ≡ cκ ]
  𝒯cctc `R-merge-box (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ cκ , cκ′ , cκ″ ←
                                      ψ(here refl) , ψ(there (here refl)) , ψ′(here refl) ]
                                cκ″ ≡ evalTick (✓ join cκ′ cκ) ]
  𝒯cctc `R-merge-lam (_ , (τₐ , τᵣ) , refl) (ϑ , tt) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ cκ , cκ′ , cκ″ ←
                                      ψ(here refl) , ψ(there (here refl)) , ψ′(here refl) ]
                                cκ″ ≡ evalTick (✓ join cκ′ cκ) ]
  𝒯cctc `R-proxy-unbox (τ , tt) (ϑ , isval) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ cκ , cκ′ ← ψ(here refl) , ψ′(here refl) ]
                                cκ′ ≡ box/cc-cκ cκ ]
  𝒯cctc `R-proxy-β (τᵣ , τₐ) (ϑ , isval) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ cκ , cκₐ , cκᵣ ←
                                      ψ(here refl) , ψ′(here refl) , ψ′(there (here refl)) ]
                                cκₐ ≡ →/cc-dom-cκ cκ ×
                                cκᵣ ≡ →/cc-rng-cκ cκ ]
