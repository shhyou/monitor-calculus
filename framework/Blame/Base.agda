{-# OPTIONS --without-K --safe #-}

module Blame.Base (Label : Set) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; subst; trans)

open import Data.Unit.Base as Unit using (⊤; tt) -- needed for the number typeclass
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_; curry; uncurry)

open import Data.List.Base as List using (List; []; _∷_; length; lookup; _++_; map; reverse)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)

open import Function.Base using (id; const; constᵣ; _∘_)

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Language

open import Contract.Common Label

import TransitionRelationUtil

record Blame : Set where
  inductive
  eta-equality
  constructor ⟨_,_⟩ᵇ
  field
    bpos : Label
    bneg : Label
open Blame public

blame-swap : Blame → Blame
blame-swap b = ⟨ bneg b , bpos b ⟩ᵇ

signed-blame : Sgn → Blame → Blame
signed-blame pos b = b
signed-blame neg b = blame-swap b

blame-swap-sgn-negate : ∀ ± b → blame-swap (signed-blame ± b) ≡ signed-blame (negate ±) b
blame-swap-sgn-negate pos b = refl
blame-swap-sgn-negate neg b = refl


𝒜blameobj : AnnTerm
AnnTerm.Ann   𝒜blameobj τ = List Blame
AnnTerm.State 𝒜blameobj   = ⊤

𝒜owner : AnnTerm
AnnTerm.Ann   𝒜owner τ = Label × Label
AnnTerm.State 𝒜owner   = ⊤


module AnnBlameContractLang (𝒜 : AnnTerm) where
  open import Contract.Base Label 𝒜

  --    the owner of the context (outer); the owner of the expr (inner); contracts paired with blames
  𝒜blame-sctc : AnnTerm
  AnnTerm.Ann   𝒜blame-sctc τ = (Label × Label) × List (Blame × SCtc1N [] τ)
  AnnTerm.State 𝒜blame-sctc   = Status

  𝒜blame : AnnTerm
  AnnTerm.Ann   𝒜blame τ = List (Blame × SCtc1N [] τ)
  AnnTerm.State 𝒜blame   = Status

  𝒜blame-sctc-owner-view : AnnTermView 𝒜blame-sctc 𝒜owner
  𝒜blame-sctc-owner-view = mkView proj₁
                                  (const tt)
                                  constᵣ
                                  (λ s₁ → refl)
                                  (λ s₁ s₂ → refl)
                                  (λ s₁ s₂ s₂′ → refl)

  𝒜blame-sctc-blame-view : AnnTermView 𝒜blame-sctc 𝒜blame
  𝒜blame-sctc-blame-view = mkView proj₂
                                  id
                                  const
                                  (λ s₁ → refl)
                                  (λ s₁ s₂ → refl)
                                  (λ s₁ s₂ s₂′ → refl)

  𝒜blame-sctc-view : AnnTermView 𝒜blame 𝒜sctc
  𝒜blame-sctc-view = mkView (List.map proj₂)
                            id
                            const
                            (λ s₁ → refl)
                            (λ s₁ s₂ → refl)
                            (λ s₁ s₂ s₂′ → refl)

  𝒜blame-blameobj-view : AnnTermView 𝒜blame 𝒜blameobj
  𝒜blame-blameobj-view = mkView (map proj₁)
                                (const tt)
                                constᵣ
                                (λ s₁ → refl)
                                (λ s₁ s₂ → refl)
                                (λ s₁ s₂ s₂′ → refl)


module _ {𝒜 : AnnTerm} (𝒜blameobj-view : AnnTermView 𝒜 𝒜blameobj) where
  private
    module TR = TransitionRelationUtil (ATState 𝒜)
  open AnnTermViewUtils 𝒜blameobj-view

  𝒯blame : AnnTransit 𝒜
  𝒯blame `R-cross-unit (_ , refl) (ϑ , tt) ψ ψ′ =
    TR.[ ⊤ ]
  𝒯blame `R-cross-nat (_ , refl) (ϑ , isval) ψ ψ′ =
    TR.[ ⊤ ]
  𝒯blame `R-cross-cons (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁ , isval₂) ψ ψ′ =
    TR.[ getAnn[ bs , bs₁ , bs₂ ← ψ(here refl) , ψ′(here refl) , ψ′(there (here refl)) ]
          bs₁ ≡ bs × bs₂ ≡ bs ]
  𝒯blame `R-cross-inl (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁) ψ ψ′ =
    TR.[ getAnn[ bs , bs₁ ← ψ(here refl) , ψ′(here refl) ]
          bs₁ ≡ bs ]
  𝒯blame `R-cross-inr (_ , (τ₁ , τ₂) , refl) (ϑ , isval₂) ψ ψ′ =
    TR.[ getAnn[ bs , bs₂ ← ψ(here refl) , ψ′(here refl) ]
          bs₂ ≡ bs ]
  𝒯blame `R-cross-roll (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    TR.[ getAnn[ bs , bs′ ← ψ(here refl) , ψ′(here refl) ]
          bs′ ≡ bs ]
  𝒯blame `R-cross-box (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    TR.[ getAnn[ bs , bs′ ← ψ(here refl) , ψ′(here refl) ]
          bs′ ≡ bs ]
  𝒯blame `R-cross-lam (_ , (τₐ , τᵣ) , refl) (ϑ , tt) ψ ψ′ =
    TR.[ getAnn[ bs , bs′ ← ψ(here refl) , ψ′(here refl) ]
          bs′ ≡ bs ]
  𝒯blame `R-merge-box (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    TR.[ getAnn[ bs , bs′ , bs″ ← ψ(here refl) , ψ(there (here refl)) , ψ′(here refl) ]
          bs″ ≡ bs′ ++ bs ]
  𝒯blame `R-merge-lam (_ , (τₐ , τᵣ) , refl) (ϑ , tt) ψ ψ′ =
    TR.[ getAnn[ bs , bs′ , bs″ ← ψ(here refl) , ψ(there (here refl)) , ψ′(here refl) ]
          bs″ ≡ bs′ ++ bs ]
  𝒯blame `R-proxy-unbox (τ , tt) (ϑ , isval) ψ ψ′ =
    TR.[ getAnn[ bs , bs′ ← ψ(here refl) , ψ′(here refl) ]
          bs′ ≡ bs ]
  𝒯blame `R-proxy-β (τᵣ , τₐ) (ϑ , isval) ψ ψ′ =
    TR.[ getAnn[ bs , bsₐ , bsᵣ ← ψ(here refl) , ψ′(here refl) , ψ′(there (here refl)) ]
          bsₐ ≡ reverse (map blame-swap bs) × bsᵣ ≡ bs ]

module _ {𝒜 : AnnTerm} (𝒜owner-view : AnnTermView 𝒜 𝒜owner) where
  private
    module TR = TransitionRelationUtil (ATState 𝒜)
  open AnnTermViewUtils 𝒜owner-view

  𝒯owner : AnnTransit 𝒜
  𝒯owner `R-cross-unit (_ , refl) (ϑ , tt) ψ ψ′ =
    TR.[ ⊤ ]
  𝒯owner `R-cross-nat (_ , refl) (ϑ , isval) ψ ψ′ =
    TR.[ ⊤ ]
  𝒯owner `R-cross-cons (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁ , isval₂) ψ ψ′ =
    TR.[ getAnn[ owner , owner₁ , owner₂ ← ψ(here refl) , ψ′(here refl) , ψ′(there (here refl)) ]
          owner₁ ≡ owner × owner₂ ≡ owner ]
  𝒯owner `R-cross-inl (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁) ψ ψ′ =
    TR.[ getAnn[ owner , owner₁ ← ψ(here refl) , ψ′(here refl) ]
          owner₁ ≡ owner ]
  𝒯owner `R-cross-inr (_ , (τ₁ , τ₂) , refl) (ϑ , isval₂) ψ ψ′ =
    TR.[ getAnn[ owner , owner₂ ← ψ(here refl) , ψ′(here refl) ]
          owner₂ ≡ owner ]
  𝒯owner `R-cross-roll (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    TR.[ getAnn[ owner , owner′ ← ψ(here refl) , ψ′(here refl) ]
          owner′ ≡ owner ]
  𝒯owner `R-cross-box (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    TR.[ getAnn[ owner , owner′ ← ψ(here refl) , ψ′(here refl) ]
          owner′ ≡ owner ]
  𝒯owner `R-cross-lam (_ , (τₐ , τᵣ) , refl) (ϑ , tt) ψ ψ′ =
    TR.[ getAnn[ owner , owner′ ← ψ(here refl) , ψ′(here refl) ]
          owner′ ≡ owner ]
  𝒯owner `R-merge-box (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    TR.[ getAnn[ owner , owner′ , owner″ ← ψ(here refl) , ψ(there (here refl)) , ψ′(here refl) ]
          owner″ ≡ (proj₁ owner ,′ proj₂ owner′) ×
          (proj₂ owner ≡ proj₁ owner′) ]
  𝒯owner `R-merge-lam (_ , (τₐ , τᵣ) , refl) (ϑ , tt) ψ ψ′ =
    TR.[ getAnn[ owner , owner′ , owner″ ← ψ(here refl) , ψ(there (here refl)) , ψ′(here refl) ]
          owner″ ≡ (proj₁ owner ,′ proj₂ owner′) ×
          (proj₂ owner ≡ proj₁ owner′) ]
  𝒯owner `R-proxy-unbox (τ , tt) (ϑ , isval) ψ ψ′ =
    TR.[ getAnn[ owner , owner′ ← ψ(here refl) , ψ′(here refl) ]
          owner′ ≡ owner ]
  𝒯owner `R-proxy-β (τᵣ , τₐ) (ϑ , isval) ψ ψ′ =
    TR.[ getAnn[ owner , ownerₐ , ownerᵣ ←
                  ψ(here refl) , ψ′(here refl) , ψ′(there (here refl)) ]
          ownerₐ ≡ (proj₂ owner ,′ proj₁ owner) × ownerᵣ ≡ owner ]

{-
𝒯 : ℕ → AnnTransit 𝒜blame-sctc
𝒯 zero    = ∅tr
𝒯 (suc i) = 𝒯blame  ∩tr  𝒯owner  ∩tr  (𝒯sctc 𝒜sctc-view (𝒯 i))
-}
