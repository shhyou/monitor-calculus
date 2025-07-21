{-# OPTIONS --safe --without-K #-}

module Example.Count.Annotation where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Product as Product using (Σ; _,_; proj₁; proj₂)

open import Data.List.Base as List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Syntax.Type
open import Syntax.Term
open import Annotation.Language

𝒜cnt : AnnTerm
AnnTerm.Ann   𝒜cnt τ = ⊤
AnnTerm.State 𝒜cnt = ℕ

module _ {𝒜 : AnnTerm} (𝒜view : AnnTermView 𝒜 𝒜cnt) where
  open AnnTerm 𝒜 using (Ann; State)
  open AnnTermViewUtils 𝒜view

  Inc : State → State → Set
  Inc = λ s s′ →
    (s′ ≡ putState (suc (getState s)) s)

  𝒯cnt : AnnTransit 𝒜
  𝒯cnt `R-cross-unit  (_ , refl)             (ϑ , tt)              ψ ψ′ = Inc
  𝒯cnt `R-cross-nat   (_ , refl)             (ϑ , isval)           ψ ψ′ = Inc
  𝒯cnt `R-cross-cons  (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁ , isval₂) ψ ψ′ = Inc
  𝒯cnt `R-cross-inl   (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁)          ψ ψ′ = Inc
  𝒯cnt `R-cross-inr   (_ , (τ₁ , τ₂) , refl) (ϑ , isval₂)          ψ ψ′ = Inc
  𝒯cnt `R-cross-roll  (_ , τ′ , refl)        (ϑ , isval)           ψ ψ′ = Inc
  𝒯cnt `R-cross-box   (_ , τ′ , refl)        (ϑ , isval)           ψ ψ′ = Inc
  𝒯cnt `R-cross-lam   (_ , (τₐ , τᵣ) , refl) (ϑ , tt)              ψ ψ′ = Inc
  𝒯cnt `R-merge-box   (_ , τ′ , refl)        (ϑ , isval)           ψ ψ′ = Inc
  𝒯cnt `R-merge-lam   (_ , (τₐ , τᵣ) , refl) (ϑ , tt)              ψ ψ′ = Inc
  𝒯cnt `R-proxy-unbox (τ , tt)               (ϑ , isval)           ψ ψ′ = Inc
  𝒯cnt `R-proxy-β     (τᵣ , τₐ)              (ϑ , isval)           ψ ψ′ = Inc
