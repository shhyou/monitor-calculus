{-# OPTIONS --safe --without-K #-}

open import Annotation.Language
open import SpaceEfficient.Base
  using ()
  renaming (𝒜cctc to SE𝒜cctc)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (OrderedPredicate to SEOrderedPredicate)

module SpaceEfficient.Properties.UniqueSublist
  (Label : Set)
  {𝒜 : AnnTerm}
  (𝒜cctc-view : AnnTermView 𝒜 (SE𝒜cctc Label 𝒜))
  (OP : SEOrderedPredicate Label 𝒜 (AnnTermView.getState 𝒜cctc-view) (AnnTermView.putState 𝒜cctc-view))
  where

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst; sym; trans; cong)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties as Nat using (≤-refl; ≤-trans; module ≤-Reasoning)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; _++_; [_]; length; map)
import Data.List.Properties as List
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Relation.Binary.Permutation.Propositional as ListPerm
  -- not importing (refl; trans) to ambiguous name
  using (_↭_; prep; swap; ↭-refl; ↭-sym; ↭-trans; module PermutationReasoning)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as ListPerm
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as ListMembership

open import Function.Base using (id; flip′)

open import Data.Tick using (Tick; evalTick; ✓_)
open import Syntax.Type
open import Syntax.Term

open import Contract.Base Label 𝒜
open SpaceEfficient.OrderedPredicate Label 𝒜
open SpaceEfficient.Base Label 𝒜
open AnnTerm 𝒜 hiding (State)

open OrderedPredicate OP renaming (isPartialOrder to opIsPartialOrder)
open SECtcTransitSteps 𝒜cctc-view stronger?

private variable
  A : Set
  x : A
  xs ys zs : List A




-- type for finite, unique subset, i.e. xs ⊆ ys where elements of xs are distinct (assuming ys are)
record USublist (xs : List A) (ys : List A) : Set where
  inductive; no-eta-equality; pattern
  constructor ⟨_⟩#
  field
    {complement} : List A
    permutation : ys ↭ xs ++ complement

_⊇#_ : (ys xs : List A) → Set
_⊇#_ = flip′ USublist

USublist-length : USublist {A} xs ys → length xs ≤ length ys
USublist-length {xs = xs} {ys} xs#⊆ys@(⟨ ys↭xs ⟩#) = begin
  length xs              ≤⟨ Nat.m≤m+n (length xs) _ ⟩
  length xs + length xsᶜ ≡⟨ List.length-++ xs ⟨
  length (xs ++ xsᶜ)     ≡⟨ ListPerm.↭-length ys↭xs ⟨
  length ys              ∎ where open ≤-Reasoning; xsᶜ = USublist.complement xs#⊆ys

usublist-weaken : USublist {A} (x ∷ xs) ys → USublist xs ys
usublist-weaken {x = x} {xs = xs} {ys = ys} x∷xs#⊆ys =
  ⟨ begin
      ys
    ↭⟨ USublist.permutation x∷xs#⊆ys ⟩
      x ∷ xs ++ _
    ↭⟨ ListPerm.shift x xs _ ⟨
      xs ++ [ x ] ++ _
    ∎ ⟩#
  where open PermutationReasoning

usublist-trans : ys ↭ zs → USublist {A} xs ys → USublist xs zs
usublist-trans ys↭zs ⟨ ys↭xs++compl ⟩# = ⟨ ↭-trans (↭-sym ys↭zs) ys↭xs++compl ⟩#

usublist-prep : ∀ x → USublist {A} xs ys → USublist (x ∷ xs) (x ∷ ys)
usublist-prep x ⟨ ys↭xs++compl ⟩# = ⟨ prep x ys↭xs++compl ⟩#


usublist-drop : ∀ {ord-preds′ Δ} preds′ e →
  USublist (map flat-pred preds′) (e ∷ ord-preds′) →
  USublist (map flat-pred (evalTick (✓ drop {Δ} preds′ e))) ord-preds′
usublist-drop []                   e []#⊆e∷U′ = ⟨ ↭-refl ⟩#
usublist-drop (flat l e′ ∷ preds′) e c#⊆e∷U′ with stronger? e e′ in stronger-eq
... | true  because _ = usublist-drop preds′ e (usublist-weaken c#⊆e∷U′)
... | false because _
  with ListPerm.∈-resp-↭ (↭-sym (USublist.permutation c#⊆e∷U′)) (here refl)
    -- cong True stronger-eq : True (stronger? e e′) ≡ ⊥ where e ≡ e′ via here refl
... | here refl = ⊥-elim (subst id (cong True stronger-eq) stronger?-reflexive)
... | there e′∈ord-preds′
  with ord-preds₁′ , ord-preds₂′ , refl ← ListMembership.∈-∃++ e′∈ord-preds′ =
  usublist-trans  (↭-sym (ListPerm.shift e′ ord-preds₁′ ord-preds₂′))
                  (usublist-prep e′ (usublist-drop preds′ e preds′#⊆e∷preds₁′++preds₂′))
  where
    open PermutationReasoning
    preds′#⊆e∷preds₁′++preds₂′ =
      ⟨ ListPerm.drop-∷ (begin
        e′ ∷ e ∷ ord-preds₁′ ++ ord-preds₂′
      ↭⟨ swap e′ e ↭-refl ⟩
        e ∷ e′ ∷ ord-preds₁′ ++ ord-preds₂′
      ↭⟨ prep e (ListPerm.shift e′ ord-preds₁′ ord-preds₂′) ⟨
        e ∷ ord-preds₁′ ++ [ e′ ] ++ ord-preds₂′
      ↭⟨ USublist.permutation c#⊆e∷U′ ⟩
        e′ ∷ map flat-pred preds′ ++ _
      ∎) ⟩#


usublist-join-flats : ∀ {Δ} preds {preds′} →
  USublist (map flat-pred preds) ord-preds →
  USublist (map flat-pred preds′) ord-preds →
  USublist (map flat-pred (evalTick (✓ join-flats {Δ} preds preds′))) ord-preds
usublist-join-flats []                 []#⊆U       c′#⊆U = c′#⊆U
usublist-join-flats (flat l e ∷ preds) ⟨ U↭c++t ⟩# c′#⊆U =
  usublist-trans (↭-sym U↭c++t)
    (usublist-prep e
      (usublist-drop _ e (usublist-trans U↭c++t
                          (usublist-join-flats preds (usublist-weaken ⟨ U↭c++t ⟩#) c′#⊆U))))
