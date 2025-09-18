{-# OPTIONS --without-K --safe #-}

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)

open import Syntax.Type
open import Syntax.Term
open import Annotation.Language

module Example.SimpleContract.ExtensibleAnnotation (m : ℕ) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Product.Base as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_ ; _,′_)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (id)

open import Syntax.Template
open import OpSemantics.Base

import TransitionRelationUtil

private
  variable
    Δ Δ′ : TCtxt
    τ τ₁ τ₂ τₐ τᵣ : TyN Δ

data CtcN : (Δ : TCtxt) → TyN Δ → Set where
  `_    : (a : tt ∈ Δ) → CtcN Δ (` a)
  1/c   : CtcN Δ `1
  flat  : (Pₘ : Fin m) → CtcN Δ `ℕ
  _*/c_ : CtcN Δ τ₁ → CtcN Δ τ₂ → CtcN Δ (τ₁ `* τ₂)
  _+/c_ : CtcN Δ τ₁ → CtcN Δ τ₂ → CtcN Δ (τ₁ `+ τ₂)
  box/c : CtcN Δ τ → CtcN Δ (Box τ)
  _→/c_ : CtcN Δ τₐ → CtcN Δ τᵣ → CtcN Δ (τₐ `→ τᵣ)
  μ/c_  : CtcN (tt ∷ Δ) τ → CtcN Δ (μ τ)

data Status : Set where
  Ok  : Status
  Err : Status

𝒜ctc : AnnTerm
AnnTerm.Ann   𝒜ctc τ = CtcN [] τ
AnnTerm.State 𝒜ctc   = Status


κ0mapsto [κ0↦_] : CtcN Δ τ → (a : tt ∈ (tt ∷ Δ)) → CtcN Δ ([t0↦ τ ] a)
κ0mapsto κ (here refl) = κ
κ0mapsto κ (there x∈Δ) = ` x∈Δ

[κ0↦_] = κ0mapsto

κrename :
  CtcN Δ τ →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  CtcN Δ′ (trename τ ren)
κrename (` a)       ren = ` (ren a)
κrename 1/c         ren = 1/c
κrename (flat Pₘ)   ren = flat Pₘ
κrename (κ₁ */c κ₂) ren = κrename κ₁ ren */c κrename κ₂ ren
κrename (κ₁ +/c κ₂) ren = κrename κ₁ ren +/c κrename κ₂ ren
κrename (box/c κ)   ren = box/c (κrename κ ren)
κrename (κₐ →/c κᵣ) ren = κrename κₐ ren →/c κrename κᵣ ren
κrename (μ/c κ)     ren = μ/c (κrename κ (pext ren))

κext :
  {σ : tt ∈ Δ → TyN Δ′} →
  (σκ : (a : tt ∈ Δ) → CtcN Δ′ (σ a)) →
  (a : tt ∈ (tt ∷ Δ)) → CtcN (tt ∷ Δ′) (text σ a)
κext σκ (here refl) = ` (here refl)
κext σκ (there x∈Δ) = κrename (σκ x∈Δ) there

κsubst :
  {σ : tt ∈ Δ → TyN Δ′} →
  CtcN Δ τ →
  (σκ : (a : tt ∈ Δ) → CtcN Δ′ (σ a)) →
  CtcN Δ′ (tsubst τ σ)
κsubst (` a)       σκ = σκ a
κsubst 1/c         σκ = 1/c
κsubst (flat Pₘ)   σκ = flat Pₘ
κsubst (κ₁ */c κ₂) σκ = κsubst κ₁ σκ */c κsubst κ₂ σκ
κsubst (κ₁ +/c κ₂) σκ = κsubst κ₁ σκ +/c κsubst κ₂ σκ
κsubst (box/c κ)   σκ = box/c (κsubst κ σκ)
κsubst (κₐ →/c κᵣ) σκ = κsubst κₐ σκ →/c κsubst κᵣ σκ
κsubst (μ/c κ)     σκ = μ/c (κsubst κ (κext σκ))

flat-pred : CtcN Δ `ℕ → Fin m
flat-pred (flat Pₘ) = Pₘ

*/c-κ₁ : CtcN Δ (τ₁ `* τ₂) → CtcN Δ τ₁
*/c-κ₁ (κ₁ */c κ₂) = κ₁

*/c-κ₂ : CtcN Δ (τ₁ `* τ₂) → CtcN Δ τ₂
*/c-κ₂ (κ₁ */c κ₂) = κ₂

+/c-κ₁ : CtcN Δ (τ₁ `+ τ₂) → CtcN Δ τ₁
+/c-κ₁ (κ₁ +/c κ₂) = κ₁

+/c-κ₂ : CtcN Δ (τ₁ `+ τ₂) → CtcN Δ τ₂
+/c-κ₂ (κ₁ +/c κ₂) = κ₂

box/c-κ : CtcN Δ (Box τ) → CtcN Δ τ
box/c-κ (box/c κ) = κ

→/c-dom-κ : CtcN Δ (τₐ `→ τᵣ) → CtcN Δ τₐ
→/c-dom-κ (κₐ →/c κᵣ) = κₐ

→/c-rng-κ : CtcN Δ (τₐ `→ τᵣ) → CtcN Δ τᵣ
→/c-rng-κ (κₐ →/c κᵣ) = κᵣ

μ/c-κ : CtcN Δ (μ τ) → CtcN Δ (tsubst τ [t0↦ μ τ ])
μ/c-κ (μ/c κ) = κsubst κ [κ0↦ (μ/c κ) ]

μ/c-κ′ : CtcN Δ (μ τ) → CtcN (tt ∷ Δ) τ
μ/c-κ′ (μ/c κ) = κ


module MonRules (𝒜 : AnnTerm)
                (Pred⟦_⟧ : Fin m → ∀ {v} → ATAnn 𝒜 ∣ v isvalof `ℕ → Bool)
                (𝒜ctc-view : AnnTermView 𝒜 𝒜ctc)
  where
  open AnnTerm 𝒜 using (Ann; State)
  open AnnTermViewUtils 𝒜ctc-view

  private
    variable
      𝒯 : AnnTransit 𝒜
      e : Ann ∣ [] ⊢ τ
      v : Ann ∣ [] ⊢ τ
    module TR = TransitionRelationUtil State

  𝒯c : AnnTransit 𝒜
  𝒯c `R-cross-unit  (_ , refl)             (ϑ , tt)              ψ ψ′ =
    guardState Ok
  𝒯c `R-cross-nat   (_ , refl)             (ϑ , isval)           ψ ψ′ =
    guardState Ok  TR.∘
    λ s s′ →
      getAnn[ κ ← ψ(here refl) ]
        s′ ≡ putState (if (Pred⟦ flat-pred κ ⟧ isval) then Ok else Err) s
  𝒯c `R-cross-cons  (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁ , isval₂) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ κ , κ₁ , κ₂ ← ψ(here refl) , ψ′(here refl) , ψ′(there (here refl)) ]
                                κ₁ ≡ */c-κ₁ κ ×
                                κ₂ ≡ */c-κ₂ κ ]
  𝒯c `R-cross-inl   (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁)          ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ κ , κ′ ← ψ(here refl) , ψ′(here refl) ]
                                κ′ ≡ +/c-κ₁ κ ]
  𝒯c `R-cross-inr   (_ , (τ₁ , τ₂) , refl) (ϑ , isval₂)          ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ κ , κ′ ← ψ(here refl) , ψ′(here refl) ]
                                κ′ ≡ +/c-κ₂ κ ]
  𝒯c `R-cross-roll  (_ , τ′ , refl)        (ϑ , isval)           ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ κ , κ′ ← ψ(here refl) , ψ′(here refl) ]
                                κ′ ≡ μ/c-κ κ ]
  𝒯c `R-cross-box   (_ , τ′ , refl)        (ϑ , isval)           ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ κ , κ′ ← ψ(here refl) , ψ′(here refl) ]
                                κ′ ≡ κ ]
  𝒯c `R-cross-lam   (_ , (τₐ , τᵣ) , refl) (ϑ , tt)              ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ κ , κ′ ← ψ(here refl) , ψ′(here refl) ]
                                κ′ ≡ κ ]
  𝒯c `R-merge-box   (_ , τ′ , refl)        (ϑ , isval)           ψ ψ′ =
    TR.[ ⊥ ]
  𝒯c `R-merge-lam   (_ , (τₐ , τᵣ) , refl) (ϑ , tt)              ψ ψ′ =
    TR.[ ⊥ ]
  𝒯c `R-proxy-unbox (τ , tt)               (ϑ , isval)           ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ κ , κ′ ← ψ(here refl) , ψ′(here refl) ]
                                κ′ ≡ box/c-κ κ ]
  𝒯c `R-proxy-β     (τᵣ , τₐ)              (ϑ , isval)           ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ κ , κₐ , κᵣ ← ψ(here refl) , ψ′(here refl) , ψ′(there (here refl)) ]
                                κₐ ≡ →/c-dom-κ κ ×
                                κᵣ ≡ →/c-rng-κ κ ]
