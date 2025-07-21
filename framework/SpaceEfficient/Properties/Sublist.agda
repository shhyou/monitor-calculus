{-# OPTIONS --without-K --safe #-}

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Data.Unit.Base as Unit using (⊤; tt)

open import Annotation.Language
open import SpaceEfficient.Base
  using ()
  renaming (𝒜cctc to SE𝒜cctc)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (Pred to SEPred)

module SpaceEfficient.Properties.Sublist
  (Label : Set)
  {𝒜 : AnnTerm}
  (𝒜cctc-view : AnnTermView 𝒜 (SE𝒜cctc Label 𝒜))
  (stronger? : SEPred Label 𝒜 → SEPred Label 𝒜 → Dec ⊤)
  where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst; sym; trans; cong; module ≡-Reasoning)

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s; _⊔_; _⊓_)
open import Data.Nat.Properties as Nat
  using (≤-refl; ≤-trans; module ≤-Reasoning)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; _++_; [_]; length; map)
import Data.List.Properties as List
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Sublist.Propositional as ListSub
  using (_⊆_; []; _∷ʳ_; _∷_)
import Data.List.Relation.Binary.Sublist.Propositional.Properties as ListSub

open import Data.Tick using (Tick; evalTick; execTick; ✓_)

open import Syntax.Type
open import Syntax.Term

open import Contract.Common Label
open import Contract.Base Label 𝒜
open SpaceEfficient.Base Label 𝒜
open AnnTerm 𝒜 hiding (State)

open SECtcTransitSteps 𝒜cctc-view stronger?


sublist-drop : ∀ {Δ} preds′ e →
  evalTick (✓ drop {Δ} preds′ e) ⊆ preds′
sublist-drop []                   e = []
sublist-drop (flat l e′ ∷ preds′) e with stronger? e e′
... | true  because _ = flat l e′ ∷ʳ sublist-drop preds′ e
... | false because _ = refl ∷ sublist-drop preds′ e

sublist-join-flats : ∀ {Δ} preds preds′ →
  evalTick (✓ join-flats {Δ} preds preds′) ⊆ preds ++ preds′
sublist-join-flats []                 preds′ = ListSub.⊆-reflexive refl
sublist-join-flats (flat l e ∷ preds) preds′ =
  refl ∷ ListSub.⊆-trans  (sublist-drop (evalTick (✓ join-flats preds preds′)) e)
                          (sublist-join-flats preds preds′)


drop-length : ∀ {Δ} preds e →
  length (evalTick (✓ drop {Δ} preds e)) ≤ length preds
drop-length preds e = ListSub.length-mono-≤ (sublist-drop preds e)

join-flats-length : ∀ {Δ} preds preds′ →
  length (evalTick (✓ join-flats {Δ} preds preds′)) ≤ length (preds ++ preds′)
join-flats-length preds preds′ = ListSub.length-mono-≤ (sublist-join-flats preds preds′)


drop-⊆-mono-≤ : ∀ {Δ preds preds′} →
  preds ⊆ preds′ →
  ∀ e →
  execTick (✓ drop {Δ} preds e) ≤ execTick (✓ drop {Δ} preds′ e)
drop-⊆-mono-≤ [] e = ≤-refl
drop-⊆-mono-≤ {preds = preds} {preds′ = _ ∷ preds′} (flat l e′ ∷ʳ preds⊆preds′) e with stronger? e e′
... | true  because _ = ≤-trans (drop-⊆-mono-≤ preds⊆preds′ e) (Nat.m≤n+m _ 3)
... | false because _ = begin
    execTick (✓ drop preds e)
  ≤⟨ drop-⊆-mono-≤ preds⊆preds′ e ⟩
    execTick (✓ drop preds′ e)
  ≤⟨ Nat.m≤n+m _ 4 ⟩
    4 + execTick (✓ drop preds′ e)
  ≡⟨ cong (3 +_) (Nat.+-comm 1 _) ⟩
    3 + (execTick (✓ drop preds′ e) + 1) ∎
  where open ≤-Reasoning
drop-⊆-mono-≤ {preds = flat l e′ ∷ _} (refl ∷ preds⊆preds′) e with stronger? e e′
... | true  because _ = Nat.+-monoʳ-≤ 3 (drop-⊆-mono-≤ preds⊆preds′ e)
... | false because _ = Nat.+-monoʳ-≤ 3 (Nat.+-monoˡ-≤ 1 (drop-⊆-mono-≤ preds⊆preds′ e))
