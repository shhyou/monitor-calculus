{-# OPTIONS --safe --without-K #-}

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Data.Unit.Base as Unit using (⊤; tt)

open import Annotation.Language
open import SpaceEfficient.Base
  using ()
  renaming (𝒜cctc to SE𝒜cctc)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (Pred to SEPred)

module SpaceEfficient.Properties.Size
  (Label : Set)
  {𝒜 : AnnTerm}
  (𝒜cctc-view : AnnTermView 𝒜 (SE𝒜cctc Label 𝒜))
  (stronger? : SEPred Label 𝒜 → SEPred Label 𝒜 → Dec ⊤)
  where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst; sym; trans; cong; module ≡-Reasoning)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties as Nat
  using (≤-refl; ≤-trans; module ≤-Reasoning)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_; ∃₂)

open import Data.List.Base as List using (List; []; _∷_; length; map)
import Data.List.Properties as List
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (_∘′_; flip′)

open import Data.NatProperties

open import Syntax.Type
open import Syntax.Term

open import Contract.Common Label
open import Contract.Base Label 𝒜
open SpaceEfficient.Base Label 𝒜
open import SpaceEfficient.LeafPredicate Label 𝒜
open import SpaceEfficient.Size Label 𝒜
open import SpaceEfficient.Height Label 𝒜
open AnnTerm 𝒜 hiding (State)

open SECtcTransitSteps 𝒜cctc-view stronger?

private variable
  h U : ℕ
  Δ : TCtxt
  Γ : Ctxt
  τ τ′ τ₁ τ₂ τₐ τᵣ : TyN Δ
  cκ : SECtcN Δ τ

cps-leaf-size-bound : SECtcPreds ((_≤ U) ∘′ length) {Δ} {τ} cκ → leaf-size cκ ≤ U
cps-leaf-size-bound (` a)            = z≤n
cps-leaf-size-bound 1/ps             = z≤n
cps-leaf-size-bound (flat/ps {preds = preds} len≤U) = subst (_≤ _) (List.length-map flat-pred preds) len≤U
cps-leaf-size-bound (cps₁ */ps cps₂) = Nat.⊔-lub (cps-leaf-size-bound cps₁) (cps-leaf-size-bound cps₂)
cps-leaf-size-bound (cps₁ +/ps cps₂) = Nat.⊔-lub (cps-leaf-size-bound cps₁) (cps-leaf-size-bound cps₂)
cps-leaf-size-bound (box/ps cps)     = cps-leaf-size-bound cps
cps-leaf-size-bound (cpsₐ →/ps cpsᵣ) = Nat.⊔-lub (cps-leaf-size-bound cpsₐ) (cps-leaf-size-bound cpsᵣ)
cps-leaf-size-bound (μ/ps cps)       = cps-leaf-size-bound cps

sectc→cps-leaf-size : ∀ cκ → SECtcPreds ((_≤ leaf-size cκ) ∘′ length) {Δ} {τ} cκ
sectc→cps-leaf-size (` a)           = ` a
sectc→cps-leaf-size 1/cc            = 1/ps
sectc→cps-leaf-size (flat/cc preds) = flat/ps (Nat.≤-reflexive (List.length-map flat-pred preds))
sectc→cps-leaf-size (cκ₁ */cc cκ₂)  =
  (cps-map (flip′ ≤-trans (Nat.m≤m⊔n (leaf-size cκ₁) (leaf-size cκ₂))) (sectc→cps-leaf-size cκ₁)) */ps
  (cps-map (flip′ ≤-trans (Nat.m≤n⊔m (leaf-size cκ₁) (leaf-size cκ₂))) (sectc→cps-leaf-size cκ₂))
sectc→cps-leaf-size (cκ₁ +/cc cκ₂)  =
  (cps-map (flip′ ≤-trans (Nat.m≤m⊔n (leaf-size cκ₁) (leaf-size cκ₂))) (sectc→cps-leaf-size cκ₁)) +/ps
  (cps-map (flip′ ≤-trans (Nat.m≤n⊔m (leaf-size cκ₁) (leaf-size cκ₂))) (sectc→cps-leaf-size cκ₂))
sectc→cps-leaf-size (box/cc cκ)     =
  box/ps (sectc→cps-leaf-size cκ)
sectc→cps-leaf-size (cκₐ →/cc cκᵣ)  =
  (cps-map (flip′ ≤-trans (Nat.m≤m⊔n (leaf-size cκₐ) (leaf-size cκᵣ))) (sectc→cps-leaf-size cκₐ)) →/ps
  (cps-map (flip′ ≤-trans (Nat.m≤n⊔m (leaf-size cκₐ) (leaf-size cκᵣ))) (sectc→cps-leaf-size cκᵣ))
sectc→cps-leaf-size (μ/cc cκ)       =
  μ/ps (sectc→cps-leaf-size cκ)

private
  c₁ : ℕ
  b : ℕ

1≤b : 1 ≤ b
2≤c₁ : 2 ≤ c₁

∀m:1≤2ᵐ : ∀ m → 1 ≤ c₁ * 2 ^ m
∀m:1≤2ᵐ m = ≤-trans (s≤s z≤n) (Nat.*-mono-≤ 2≤c₁ (Nat.^-monoʳ-≤ 2 (z≤n {m})))

1≤n⇒m≤m*n : ∀ m n → 1 ≤ n → m ≤ m * n
1≤n⇒m≤m*n m n 1≤n@(s≤s _) = Nat.m≤m*n m n -- or use {{Nat.>-nonZero 1≤n}}

sectc-node-bound : (h : ℕ) → ℕ
sectc-node-bound h = c₁ * 2 ^ h + b * (∑[ i < h ] 2 ^ i)

1≤sectc-node-bound : (h : ℕ) → 1 ≤ sectc-node-bound h
1≤sectc-node-bound h = Nat.m≤n⇒m≤n+o (b * (∑[ i < h ] 2 ^ i)) (∀m:1≤2ᵐ h)

sectc-bounded-ind : ∀ h U →
  1 ≤ U →
  SECtcMaxH {Δ} {τ} cκ h →
  SECtcPreds ((_≤ U) ∘′ length) cκ →
  sectc-size cκ ≤ sectc-node-bound h * U

sectc-bounded : ∃ λ c₀ →
  1 ≤ c₀ ×
  ∀ {Δ τ cκ h U} →
    1 ≤ U →
    SECtcMaxH {Δ} {τ} cκ h →
    SECtcPreds ((_≤ U) ∘′ length) cκ →
    sectc-size cκ ≤ c₀ * 2 ^ h * U
sectc-bounded = c₀ , 1≤c₀ ,′ λ {_} {_} {_} {h = h} {U = U} 1≤U cmh cps-len →
  ≤-trans (sectc-bounded-ind _ _ 1≤U cmh cps-len) (Nat.*-monoˡ-≤ U (bnd h))
  where open ≤-Reasoning
        c₀ = c₁ + b * 2
        1≤c₀ = ≤-trans (≤-trans (s≤s (z≤n {1})) 2≤c₁) (Nat.m≤m+n c₁ (b * 2))
        bnd : ∀ h → c₁ * 2 ^ h + b * (∑[ i < h ] 2 ^ i) ≤ c₀ * 2 ^ h
        bnd h = begin
          c₁ * 2ʰ + b * (∑[ i < h ] 2 ^ i)
            ≤⟨ Nat.+-monoʳ-≤ (c₁ * 2ʰ) (Nat.*-monoʳ-≤ b (∑-^-≤-^ h 2 ≤-refl)) ⟩
          c₁ * 2ʰ + b * 2¹⁺ʰ               ≡⟨ cong (c₁ * 2ʰ +_) (Nat.*-assoc b 2 2ʰ) ⟨
          c₁ * 2ʰ + (b * 2) * 2ʰ           ≡⟨ Nat.*-distribʳ-+ 2ʰ c₁ (b * 2) ⟨
          (c₁ + b * 2) * 2ʰ                ≡⟨⟩
          c₀ * 2ʰ                          ∎
          where 2ʰ = 2 ^ h; 2¹⁺ʰ = 2 ^ suc h

c₁ = 2
2≤c₁ = ≤-refl
b = 1
1≤b = ≤-refl

sectc-bounded-ind-two : ∀ h U (_ : 1 ≤ U) →
  1 + sectc-node-bound h * U + sectc-node-bound h * U ≤ sectc-node-bound (suc h) * U
sectc-bounded-ind-two h U 1≤U = begin
  1 + sectc-node-bound h * U + sectc-node-bound h * U
    ≡⟨ cong (1 +_) (m+m≡2m (sectc-node-bound h * U)) ⟩
  1 + 2 * (sectc-node-bound h * U)    ≡⟨ cong (1 +_) (Nat.*-assoc 2 (sectc-node-bound h) U) ⟨
  1 + 2 * sectc-node-bound h * U      ≤⟨ Nat.+-monoˡ-≤ (2 * sectc-node-bound h * U)
                                          (Nat.*-mono-≤ 1≤b 1≤U) ⟩
  b * U + 2 * sectc-node-bound h * U  ≡⟨ Nat.*-distribʳ-+ U b (2 * sectc-node-bound h) ⟨
  (b + 2 * sectc-node-bound h) * U    ≡⟨ cong (_* U) (Nat.+-comm b (2 * sectc-node-bound h)) ⟩
  (2 * sectc-node-bound h + b) * U    ≤⟨ Nat.*-monoˡ-≤ U (geometry-sum _ c₁ 2 b h ≤-refl) ⟩
  sectc-node-bound (suc h) * U        ∎ where open ≤-Reasoning

sectc-bounded-ind-one : ∀ h U (_ : 1 ≤ U) →
  1 + sectc-node-bound h * U ≤ sectc-node-bound (suc h) * U
sectc-bounded-ind-one h U 1≤U = begin
  1 + sectc-node-bound h * U                          ≤⟨ Nat.m≤m+n (1 + node-bnd) node-bnd ⟩
  1 + sectc-node-bound h * U + sectc-node-bound h * U ≤⟨ sectc-bounded-ind-two h U 1≤U ⟩
  sectc-node-bound (suc h) * U                        ∎
  where open ≤-Reasoning
        node-bnd = sectc-node-bound h * U

sectc-bounded-ind h       U 1≤U (` a)  cps-len = ≤-trans (1≤sectc-node-bound h) (1≤n⇒m≤m*n _ _ 1≤U)
sectc-bounded-ind h       U 1≤U 1/h    cps-len = ≤-trans (1≤sectc-node-bound h) (1≤n⇒m≤m*n _ _ 1≤U)
sectc-bounded-ind h       U 1≤U flat/h (flat/ps {preds = preds} |preds|≤U)  = begin
  sectc-size (flat/cc preds)        ≡⟨⟩
  length preds                      ≡⟨ List.length-map flat-pred preds ⟨
  length (map flat-pred preds)      ≡⟨ Nat.*-identityˡ _ ⟨
  1 * length (map flat-pred preds)  ≤⟨ Nat.*-mono-≤ (1≤sectc-node-bound h) |preds|≤U ⟩
  sectc-node-bound h * U            ∎
  where open ≤-Reasoning
sectc-bounded-ind {cκ = cκ₁ */cc cκ₂} (suc h) U 1≤U (cmh₁ */h cmh₂) cps-len = begin
  1 + sectc-size cκ₁ + sectc-size cκ₂
    ≤⟨ Nat.+-monoʳ-≤ 1 (Nat.+-mono-≤
        (sectc-bounded-ind h U 1≤U cmh₁ (cps-*₁ cps-len))
        (sectc-bounded-ind h U 1≤U cmh₂ (cps-*₂ cps-len))) ⟩
  1 + sectc-node-bound h * U + sectc-node-bound h * U   ≤⟨ sectc-bounded-ind-two h U 1≤U ⟩
  sectc-node-bound (suc h) * U                          ∎
  where open ≤-Reasoning
sectc-bounded-ind {cκ = cκ₁ +/cc cκ₂} (suc h) U 1≤U (cmh₁ +/h cmh₂) cps-len = begin
  1 + sectc-size cκ₁ + sectc-size cκ₂
    ≤⟨ Nat.+-monoʳ-≤ 1 (Nat.+-mono-≤
        (sectc-bounded-ind h U 1≤U cmh₁ (cps-+₁ cps-len))
        (sectc-bounded-ind h U 1≤U cmh₂ (cps-+₂ cps-len))) ⟩
  1 + sectc-node-bound h * U + sectc-node-bound h * U   ≤⟨ sectc-bounded-ind-two h U 1≤U ⟩
  sectc-node-bound (suc h) * U                          ∎
  where open ≤-Reasoning
sectc-bounded-ind {cκ = box/cc cκ} (suc h) U 1≤U (box/h cmh) cps-len = begin
  1 + sectc-size cκ             ≤⟨ Nat.+-monoʳ-≤ 1 (sectc-bounded-ind h U 1≤U cmh (cps-box cps-len)) ⟩
  1 + sectc-node-bound h * U    ≤⟨ sectc-bounded-ind-one h U 1≤U ⟩
  sectc-node-bound (suc h) * U  ∎
  where open ≤-Reasoning
sectc-bounded-ind {cκ = cκₐ →/cc cκᵣ} (suc h) U 1≤U (cmhₐ →/h cmhᵣ) cps-len = begin
  1 + sectc-size cκₐ + sectc-size cκᵣ
    ≤⟨ Nat.+-monoʳ-≤ 1 (Nat.+-mono-≤
        (sectc-bounded-ind h U 1≤U cmhₐ (cps-dom cps-len))
        (sectc-bounded-ind h U 1≤U cmhᵣ (cps-rng cps-len))) ⟩
  1 + sectc-node-bound h * U + sectc-node-bound h * U   ≤⟨ sectc-bounded-ind-two h U 1≤U ⟩
  sectc-node-bound (suc h) * U                          ∎
  where open ≤-Reasoning
sectc-bounded-ind {cκ = μ/cc cκ} (suc h) U 1≤U (μ/h cmh) cps-len = begin
  1 + sectc-size cκ             ≤⟨ Nat.+-monoʳ-≤ 1 (sectc-bounded-ind h U 1≤U cmh (cps-μ′ cps-len)) ⟩
  1 + sectc-node-bound h * U    ≤⟨ sectc-bounded-ind-one h U 1≤U ⟩
  sectc-node-bound (suc h) * U  ∎ where open ≤-Reasoning
