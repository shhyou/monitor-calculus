{-# OPTIONS --safe --without-K #-}

open import Annotation.Language
open import SpaceEfficient.Equivalence.Base
  using ()
  renaming (𝒜csctc to SE𝒜csctc; 𝒜sctc-view to SE𝒜sctc-view)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (OrderedPredicate to SEOrderedPredicate)

module SpaceEfficient.Equivalence.Simulation
  (Label : Set)
  (OP : SEOrderedPredicate  Label (SE𝒜csctc Label)
                            (AnnTermView.getState (SE𝒜sctc-view Label))
                            (AnnTermView.putState (SE𝒜sctc-view Label)))
  where

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; _≗_; subst; subst₂; sym; trans; cong)
open import Relation.Binary
  using (IsPreorder; IsEquivalence; IsPartialOrder)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties as Nat
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Sublist.Propositional as ListSub
  using (_⊆_; []; _∷_)
import Data.List.Relation.Binary.Sublist.Propositional.Properties as ListSub
open import Data.Vec.Base as Vec
  using (Vec; []; _∷_; tail; map; reverse; _++_; zipWith; cast)
import Data.Vec.Properties as Vec
open import Data.Vec.Relation.Binary.Equality.Cast
  using (≈-reflexive; ≈-sym; ≈-trans)

open import Function.Base using (id; const; _∘_)

import Data.Nat.Literals
open import Agda.Builtin.FromNat

open import Utils.Misc
open import Data.Tick using (Tick; evalTick; ✓_)
import Data.VecProperties as Vec⁺
open import Syntax.Type
open import Syntax.Term

open SpaceEfficient.Equivalence.Base Label

open import Contract.Common Label
open import Contract.Base Label 𝒜csctc
open import Contract.Vectorized Label 𝒜csctc
open SpaceEfficient.OrderedPredicate Label 𝒜csctc
open import SpaceEfficient.Base Label 𝒜csctc
open import SpaceEfficient.Sign Label 𝒜csctc

open AnnTerm 𝒜csctc using (Ann; State)
open OrderedPredicate OP renaming (isPartialOrder to opIsPartialOrder)
open SECtcTransitSteps 𝒜cctc-view stronger?




data CollapsedPreds : ∀ {Δ m} → List OPred → List (SCtc1N Δ `ℕ) → Vec (SCtc1N Δ `ℕ) m → Set where
    [] : ∀ {Δ preds-ctxt} → CollapsedPreds {Δ} preds-ctxt [] []
    _∷_ : ∀ {m Δ preds-ctxt preds sκs l} →
      (oe : OPred) →
      CollapsedPreds {Δ} {m} (oe ∷ preds-ctxt) preds                       sκs →
      CollapsedPreds {Δ}     preds-ctxt        (flat l (proj₁ oe) ∷ preds) (flat l (proj₁ oe) ∷ sκs)
    ⟨_,_,_,_⟩∷ʳ_ : ∀ {m Δ preds-ctxt preds sκs l} →
      (oe oe′ : OPred) →
      (a : oe′ ∈ preds-ctxt) →
      (oe′≼oe : oe′ ≼ oe) →
      CollapsedPreds {Δ} {m} preds-ctxt preds sκs →
      CollapsedPreds {Δ}     preds-ctxt preds (flat l (proj₁ oe) ∷ sκs)


clp-weakening : ∀ {Δ m preds-ctxt preds-ctxt′ preds sκs} →
  preds-ctxt ⊆ preds-ctxt′ →
  CollapsedPreds {Δ} {m} preds-ctxt  preds sκs →
  CollapsedPreds         preds-ctxt′ preds sκs
clp-weakening ctxt⊆ctxt′ [] = []
clp-weakening ctxt⊆ctxt′ (oe ∷ clp-preds) =
  oe ∷ clp-weakening (refl ∷ ctxt⊆ctxt′ ) clp-preds
clp-weakening ctxt⊆ctxt′ (⟨ oe , oe′ , oe′∈preds-ctxt , oe′≼oe ⟩∷ʳ clp-preds) =
  ⟨ oe , oe′ , ListSub.Any-resp-⊆ ctxt⊆ctxt′ oe′∈preds-ctxt , oe′≼oe ⟩∷ʳ
  clp-weakening ctxt⊆ctxt′ clp-preds


clprenext : ∀ {preds-ctxt preds-ctxt′} →
  (oe₀ : OPred) →
  (ren : ∀ {oe} → oe ∈ preds-ctxt → ∃[ oe′ ] oe′ ∈ preds-ctxt′ × oe′ ≼ oe) →
  ∀ {oe} → oe ∈ (oe₀ ∷ preds-ctxt) → ∃[ oe′ ] oe′ ∈ (oe₀ ∷ preds-ctxt′) × oe′ ≼ oe
clprenext oe₀ ren (here refl) = oe₀ , here refl , IsPartialOrder.reflexive opIsPartialOrder refl
clprenext oe₀ ren (there oe∈preds-ctxt) = oe₁ , there oe₁∈preds-ctxt , oe₁≼oe where
  oe₁,oe₁∈preds-ctxt,oe₁≼oe = ren oe∈preds-ctxt
  oe₁ = proj₁ oe₁,oe₁∈preds-ctxt,oe₁≼oe
  oe₁∈preds-ctxt = proj₁ (proj₂ oe₁,oe₁∈preds-ctxt,oe₁≼oe)
  oe₁≼oe = proj₂ (proj₂ oe₁,oe₁∈preds-ctxt,oe₁≼oe)


clp-rename : ∀ {Δ m preds-ctxt preds-ctxt′ preds sκs} →
  (ren : ∀ {oe} → oe ∈ preds-ctxt → ∃[ oe′ ] oe′ ∈ preds-ctxt′ × oe′ ≼ oe) →
  CollapsedPreds {Δ} {m} preds-ctxt  preds sκs →
  CollapsedPreds         preds-ctxt′ preds sκs
clp-rename ren [] = []
clp-rename ren (oe ∷ clp-preds) = oe ∷ clp-rename (clprenext oe ren) clp-preds
clp-rename ren (⟨ oe , oe₁ , oe₁∈preds-ctxt , oe₁≼oe ⟩∷ʳ clp-preds) =
  ⟨ oe , oe₀ , oe₀∈preds-ctxt′ , IsPartialOrder.trans opIsPartialOrder oe₀≼oe₁ oe₁≼oe ⟩∷ʳ
  clp-rename ren clp-preds
    where
      oe₀,oe₀∈preds-ctxt′,oe₀≼oe₁ = ren oe₁∈preds-ctxt
      oe₀ = proj₁ oe₀,oe₀∈preds-ctxt′,oe₀≼oe₁
      oe₀∈preds-ctxt′ = proj₁ (proj₂ oe₀,oe₀∈preds-ctxt′,oe₀≼oe₁)
      oe₀≼oe₁ = proj₂ (proj₂ oe₀,oe₀∈preds-ctxt′,oe₀≼oe₁)




clp-drop : ∀ {Δ m preds-ctxt preds sκs oe} →
  (oe∈preds-ctxt : oe ∈ preds-ctxt) →
  CollapsedPreds {Δ} {m} preds-ctxt preds sκs →
  CollapsedPreds preds-ctxt (evalTick (✓ drop preds (proj₁ oe))) sκs
clp-drop oe∈preds-ctxt [] = []
clp-drop {preds-ctxt = preds-ctxt} {oe = oe} oe∈preds-ctxt (oe′ ∷ clp-preds′)
  with stronger⇒≼ oe oe′  | stronger? (proj₁ oe) (proj₁ oe′) in stronger?-eq
... | to-≼ | true  because _ rewrite stronger?-eq =
  ⟨ oe′ , oe , oe∈preds-ctxt , oe≼oe′ ⟩∷ʳ
  clp-rename ren-oe′-to-oe (clp-drop (there oe∈preds-ctxt) clp-preds′) where
    oe≼oe′ = to-≼ tt
    ren-oe′-to-oe : ∀ {oe₁} →
      oe₁ ∈ (oe′ ∷ preds-ctxt) → ∃[ oe₀ ] oe₀ ∈ preds-ctxt × oe₀ ≼ oe₁
    ren-oe′-to-oe {oe₁} (here refl) = oe , oe∈preds-ctxt , oe≼oe′
    ren-oe′-to-oe {oe₁} (there oe₁∈preds-ctxt) =
      _ , oe₁∈preds-ctxt , IsPartialOrder.reflexive opIsPartialOrder refl
... | to-≼ | false because _ = oe′ ∷ clp-drop (there oe∈preds-ctxt) clp-preds′
clp-drop oe∈preds-ctxt (⟨ oe′ , oe₁′ , oe₁′∈preds-ctxt , oe₁′≼oe′ ⟩∷ʳ clp-preds′) =
  ⟨ oe′ , oe₁′ , oe₁′∈preds-ctxt , oe₁′≼oe′ ⟩∷ʳ clp-drop oe∈preds-ctxt clp-preds′


clp-join-flats : ∀ {Δ m′ m preds-ctxt preds preds′ sκs sκs′} →
  CollapsedPreds {Δ} {m} preds-ctxt preds sκs →
  CollapsedPreds {Δ} {m′} [] preds′ sκs′ →
  CollapsedPreds preds-ctxt (evalTick (✓ join-flats preds preds′)) (sκs ++ sκs′)
clp-join-flats {preds-ctxt = preds-ctxt} [] clp-preds′ =
  clp-weakening (ListSub.minimum preds-ctxt) clp-preds′
clp-join-flats (oe ∷ clp-preds) clp-preds′ =
  oe ∷ clp-drop (here refl) (clp-join-flats clp-preds clp-preds′)
clp-join-flats (⟨ oe , oe′ , oe′∈preds-ctxt , oe′≼oe ⟩∷ʳ clp-preds) clp-preds′ =
  ⟨ oe , oe′ , oe′∈preds-ctxt , oe′≼oe ⟩∷ʳ  clp-join-flats clp-preds clp-preds′




clprename : ∀ {m Δ Δ′ pred-ctxt preds sκs} →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  CollapsedPreds {Δ} pred-ctxt preds sκs →
  CollapsedPreds  {Δ′} {m}
                  pred-ctxt
                  (List.map sκflat-change-variable preds)
                  (sκsrename sκs ren)
clprename ren [] = []
clprename ren (oe ∷ clp-preds) = oe ∷ clprename ren clp-preds
clprename ren (⟨ oe , oe′ , oe′∈pred-ctxt , oe′≼oe ⟩∷ʳ clp-preds) =
  ⟨ oe , oe′ , oe′∈pred-ctxt , oe′≼oe ⟩∷ʳ clprename ren clp-preds


clpsubst : ∀ {m Δ Δ′ pred-ctxt preds sκs} →
  {σ : tt ∈ Δ → TyN Δ′} →
  (σκs : (a : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a)) m) →
  CollapsedPreds {Δ} pred-ctxt preds sκs →
  CollapsedPreds  {Δ′} {m}
                  pred-ctxt
                  (List.map sκflat-change-variable preds)
                  (sκssubst sκs σκs)
clpsubst σκs [] = []
clpsubst σκs (oe ∷ clp-preds) = oe ∷ clpsubst (tail ∘ σκs) clp-preds
clpsubst σκs (⟨ oe , oe′ , oe′∈pred-ctxt , oe′≼oe ⟩∷ʳ clp-preds) =
  ⟨ oe , oe′ , oe′∈pred-ctxt , oe′≼oe ⟩∷ʳ clpsubst (tail ∘ σκs) clp-preds




data CollapsedCtcs (m : ℕ) : ∀ {Δ τ} → SECtcN Δ τ → Vec (SCtc1N Δ τ) m → Set where
  `_ : ∀ {Δ} → (a : tt ∈ Δ) → ∀ {sκs} → CollapsedCtcs m (` a) sκs
  1/clc : ∀ {Δ sκs} → CollapsedCtcs m {Δ} 1/cc sκs
  flat/clc : ∀ {Δ preds sκs} →
    CollapsedPreds [] preds sκs →
    CollapsedCtcs m {Δ} (flat/cc preds) sκs
  _*/clc_ : ∀ {Δ τ₁ τ₂ cκ₁ cκ₂ sκs₁ sκs₂} →
    CollapsedCtcs m cκ₁ sκs₁ →
    CollapsedCtcs m cκ₂ sκs₂ →
    CollapsedCtcs m {Δ} {τ₁ `* τ₂} (cκ₁ */cc cκ₂) (zipWith _*/c_ sκs₁ sκs₂)
  _+/clc_ : ∀ {Δ τ₁ τ₂ cκ₁ cκ₂ sκs₁ sκs₂} →
    CollapsedCtcs m cκ₁ sκs₁ →
    CollapsedCtcs m cκ₂ sκs₂ →
    CollapsedCtcs m {Δ} {τ₁ `+ τ₂} (cκ₁ +/cc cκ₂) (zipWith _+/c_ sκs₁ sκs₂)
  box/clc : ∀ {Δ τ cκ sκs} →
    CollapsedCtcs m cκ sκs →
    CollapsedCtcs m {Δ} {Box τ} (box/cc cκ) (map box/c sκs)
  _→/clc_ : ∀ {Δ τₐ τᵣ cκₐ cκᵣ sκsₐ sκsᵣ} →
    CollapsedCtcs m cκₐ (reverse sκsₐ) →
    CollapsedCtcs m cκᵣ sκsᵣ →
    CollapsedCtcs m {Δ} {τₐ `→ τᵣ} (cκₐ →/cc cκᵣ) (zipWith _→/c_ sκsₐ sκsᵣ)
  μ/clc_ : ∀ {Δ τ cκ sκs} →
    CollapsedCtcs m cκ sκs →
    CollapsedCtcs m {Δ} {μ τ} (μ/cc cκ) (map μ/c_ sκs)


clc-join : ∀ {m m′ Δ τ cκ cκ′ sκs sκs′} →
  CollapsedCtcs m cκ  sκs →
  CollapsedCtcs m′ cκ′ sκs′ →
  CollapsedCtcs (m + m′) {Δ} {τ} (evalTick (✓ join cκ cκ′)) (sκs ++ sκs′)
clc-join (` a) (` .a) = ` a
clc-join 1/clc 1/clc  = 1/clc
clc-join {m} {m′} {cκ = flat/cc preds} {flat/cc preds′} (flat/clc clp) (flat/clc clp′)
  = flat/clc (clp-join-flats clp clp′)
clc-join {m} {m′} {cκ = cκ} {cκ′}
  (_*/clc_ {sκs₁ = sκs₁} {sκs₂ = sκs₂} clc₁ clc₂)
  (_*/clc_ {sκs₁ = sκs₁′} {sκs₂ = sκs₂′} clc₁′ clc₂′)
  rewrite sym (Vec.zipWith-++ _*/c_ sκs₁ sκs₁′ sκs₂ sκs₂′)
  = (clc-join clc₁ clc₁′) */clc (clc-join clc₂ clc₂′)
clc-join {m} {m′} {cκ = cκ} {cκ′}
  (_+/clc_ {sκs₁ = sκs₁} {sκs₂ = sκs₂} clc₁ clc₂)
  (_+/clc_ {sκs₁ = sκs₁′} {sκs₂ = sκs₂′} clc₁′ clc₂′)
  rewrite sym (Vec.zipWith-++ _+/c_ sκs₁ sκs₁′ sκs₂ sκs₂′)
  = (clc-join clc₁ clc₁′) +/clc (clc-join clc₂ clc₂′)
clc-join {m} {m′} {cκ = cκ} {cκ′}
  (box/clc {sκs = sκs} clc)
  (box/clc {sκs = sκs′} clc′)
  rewrite sym (Vec.map-++ box/c sκs sκs′)
  = box/clc (clc-join clc clc′)
clc-join {m} {m′} {Δ = Δ} {τ = τₐ `→ τᵣ} {cκ = cκₐ →/cc cκᵣ} {cκₐ′ →/cc cκᵣ′}
  (_→/clc_ {sκsₐ = sκsₐ} {sκsᵣ = sκsᵣ} clcₐ clcᵣ)
  (_→/clc_ {sκsₐ = sκsₐ′} {sκsᵣ = sκsᵣ′} clcₐ′ clcᵣ′)
  rewrite sym (Vec.zipWith-++ _→/c_ sκsₐ sκsₐ′ sκsᵣ sκsᵣ′)
  = substd-clcₐ →/clc (clc-join clcᵣ clcᵣ′) where
      m′+m≡m+m′ : m′ + m ≡ m + m′
      m′+m≡m+m′ = Nat.+-comm m′ m

      rev-sκs++rev-sκs : Vec (SCtc1N Δ τₐ) (m′ + m)
      rev-sκs++rev-sκs = reverse sκsₐ′ ++ reverse sκsₐ

      rev-sκs++sκs-eq : cast m′+m≡m+m′ rev-sκs++rev-sκs ≡ reverse (sκsₐ ++ sκsₐ′)
      rev-sκs++sκs-eq = ≈-sym (Vec⁺.reverse-++ sκsₐ sκsₐ′)

      substd-clcₐ : CollapsedCtcs (m + m′)
                                  (evalTick (✓ join cκₐ′ cκₐ))
                                  (reverse (sκsₐ ++ sκsₐ′))
      substd-clcₐ = substd  (λ n xs → CollapsedCtcs n (evalTick (✓ join cκₐ′ cκₐ)) xs)
                            m′+m≡m+m′
                            (subst (_≡ reverse (sκsₐ ++ sκsₐ′))
                                   (sym (Vec.subst-is-cast m′+m≡m+m′ rev-sκs++rev-sκs))
                                   rev-sκs++sκs-eq)
                            (clc-join clcₐ′ clcₐ)
clc-join {m} {m′} {cκ = cκ} {cκ′}
  (μ/clc_ {sκs = sκs} clc)
  (μ/clc_ {sκs = sκs′} clc′)
  rewrite sym (Vec.map-++ μ/c_ sκs sκs′)
  = μ/clc (clc-join clc clc′)




signed-reverse : ∀ {m} {A : Set} → Sgn → Vec A m → Vec A m
signed-reverse pos = id
signed-reverse neg = reverse

record ClpCtcSpace (m : ℕ) {Δ′ : TCtxt} (± : Sgn) (τ : TyN Δ′) : Set where
  no-eta-equality
  field
    cκ : SECtcN Δ′ τ
    sκs : Vec (SCtc1N Δ′ τ) m
    clc : CollapsedCtcs m cκ (signed-reverse ± sκs)


clcrename : ∀ {m Δ Δ′ τ} →
  {cκ : SECtcN Δ τ} →
  {sκs : Vec (SCtc1N Δ τ) m} →
  CollapsedCtcs m cκ sκs →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  CollapsedCtcs m (cκrename cκ ren) (sκsrename sκs ren)
clcrename (` a) ren = ` (ren a)
clcrename 1/clc ren = 1/clc
clcrename (flat/clc clp-preds) ren = flat/clc (clprename ren clp-preds)
clcrename (_*/clc_ {sκs₁ = sκs₁} {sκs₂ = sκs₂} clc₁ clc₂) ren
  rewrite sκsrename-*/c-comm sκs₁ sκs₂ ren
  = (clcrename clc₁ ren) */clc (clcrename clc₂ ren)
clcrename (_+/clc_ {sκs₁ = sκs₁} {sκs₂ = sκs₂} clc₁ clc₂) ren
  rewrite sκsrename-+/c-comm sκs₁ sκs₂ ren
  = (clcrename clc₁ ren) +/clc (clcrename clc₂ ren)
clcrename (box/clc {sκs = sκs} clc) ren
  rewrite sκsrename-box/c-comm sκs ren
  = box/clc (clcrename clc ren)
clcrename {m} {cκ = cκₐ →/cc cκᵣ}
  (_→/clc_ {sκsₐ = sκsₐ} {sκsᵣ = sκsᵣ} clcₐ clcᵣ) ren
  rewrite sκsrename-→/c-comm sκsₐ sκsᵣ ren
          {- | sκsrename-reverse-comm sκsₐ ren -} -- not fired
  = substd-clcₐ →/clc (clcrename clcᵣ ren) where
      substd-clcₐ : CollapsedCtcs m (cκrename cκₐ ren) (reverse (sκsrename sκsₐ ren))
      substd-clcₐ rewrite sκsrename-reverse-comm sκsₐ ren = clcrename clcₐ ren
clcrename (μ/clc_ {sκs = sκs} clc) ren
  rewrite sκsrename-μ/c-comm sκs ren
  = μ/clc (clcrename clc (pext ren))




clcext : ∀ {± m Δ Δ′} {δ : All (const Sgn) Δ}
  {σ : tt ∈ Δ → TyN Δ′} →
  {σc : (a : tt ∈ Δ) → SECtcN Δ′ (σ a)} →
  {σκs : (a : tt ∈ Δ) → Vec (SCtc1N Δ′ (σ a)) m} →
  (σclc : (a : tt ∈ Δ) → CollapsedCtcs m (σc a) (signed-reverse (ListAll.lookup δ a) (σκs a))) →
  (a : tt ∈ (tt ∷ Δ)) →
    CollapsedCtcs m (cκext σc a) (signed-reverse (ListAll.lookup (± ∷ δ) a) (sκsext σκs a))
clcext σclc (here refl) = ` here refl
clcext {± = ±} {δ = δ} {σκs = σκs} σclc (there x∈Δ) rewrite sκsext-rename σκs x∈Δ
  with clcrename (σclc x∈Δ) there
... | σclc-renamed
  with ListAll.lookup (± ∷ δ) (there x∈Δ) in ±∷δ[1+x∈Δ]-eq | ListAll.lookup δ x∈Δ in δ[x∈Δ]-eq
... | pos | neg = ⊥-elim (pos≢neg (trans (sym ±∷δ[1+x∈Δ]-eq) δ[x∈Δ]-eq))
... | neg | pos = ⊥-elim (pos≢neg (trans (sym δ[x∈Δ]-eq) ±∷δ[1+x∈Δ]-eq))
... | pos | pos = σclc-renamed
... | neg | neg rewrite sκsrename-reverse-comm (σκs x∈Δ) there = σclc-renamed


clsext : ∀ {m ± Δ Δ′} {δ : All (const Sgn) Δ}
  {σ : tt ∈ Δ → TyN Δ′} →
  (σcls : (a : tt ∈ Δ) → ClpCtcSpace m (ListAll.lookup δ a) (σ a)) →
  (a : tt ∈ (tt ∷ Δ)) →
    ClpCtcSpace m (ListAll.lookup (± ∷ δ) a) (text σ a)
clsext σcls a = record  { cκ = cκext (ClpCtcSpace.cκ ∘ σcls) a
                        ; sκs = sκsext (ClpCtcSpace.sκs ∘ σcls) a
                        ; clc = clcext (ClpCtcSpace.clc ∘ σcls) a }




mutual
  clcsubst-pos : ∀ {m Δ Δ′ δ δ′ τ} →
    {σ : tt ∈ Δ → TyN Δ′} →
    {cκ : SECtcN Δ τ} →
    {sκs : Vec (SCtc1N Δ τ) m} →
    CollapsedCtcs m cκ sκs →
    SECtcSigned pos δ cκ →
    (σcls : (a : tt ∈ Δ) → ClpCtcSpace m (ListAll.lookup δ a) (σ a)) →
    (σp : (a : tt ∈ Δ) → SECtcSigned (ListAll.lookup δ a) δ′ (ClpCtcSpace.cκ (σcls a))) →
    CollapsedCtcs m (cκsubst cκ (ClpCtcSpace.cκ ∘ σcls))
                    (sκssubst sκs (ClpCtcSpace.sκs ∘ σcls))
  clcsubst-pos {δ = δ} {sκs = sκs} (` a) (var/p .a lookup-eq) σcls σp
    rewrite sκssubst-a-comm a sκs (ClpCtcSpace.sκs ∘ σcls)
          | cong (λ ± → signed-reverse ± (ClpCtcSpace.sκs (σcls a))) lookup-eq
    = ClpCtcSpace.clc (σcls a)
  clcsubst-pos 1/clc pmκ σcls σp = 1/clc
  clcsubst-pos (flat/clc {sκs = sκs} clp-preds) pmκ σcls σp =
    flat/clc (clpsubst (ClpCtcSpace.sκs ∘ σcls) clp-preds)
  clcsubst-pos (_*/clc_ {sκs₁ = sκs₁} {sκs₂ = sκs₂} clc₁ clc₂) (pmκ₁ */p pmκ₂) σcls σp
    rewrite sκssubst-*/c-comm sκs₁ sκs₂ (ClpCtcSpace.sκs ∘ σcls)
    = (clcsubst-pos clc₁ pmκ₁ σcls σp) */clc (clcsubst-pos clc₂ pmκ₂ σcls σp)
  clcsubst-pos (_+/clc_ {sκs₁ = sκs₁} {sκs₂ = sκs₂} clc₁ clc₂) (pmκ₁ +/p pmκ₂) σcls σp
    rewrite sκssubst-+/c-comm sκs₁ sκs₂ (ClpCtcSpace.sκs ∘ σcls)
    = (clcsubst-pos clc₁ pmκ₁ σcls σp) +/clc (clcsubst-pos clc₂ pmκ₂ σcls σp)
  clcsubst-pos (box/clc {sκs = sκs} clc) (box/p pmκ) σcls σp
    rewrite sκssubst-box/c-comm sκs (ClpCtcSpace.sκs ∘ σcls)
    = box/clc (clcsubst-pos clc pmκ σcls σp)
  clcsubst-pos {m = m} {cκ = cκₐ →/cc cκᵣ}
    (_→/clc_ {sκsₐ = sκsₐ} {sκsᵣ = sκsᵣ} clcₐ clcᵣ) (pmκₐ →/p pmκᵣ) σcls σp
    rewrite sκssubst-→/c-comm sκsₐ sκsᵣ (ClpCtcSpace.sκs ∘ σcls)
    = substd-clcₐ →/clc (clcsubst-pos clcᵣ pmκᵣ σcls σp) where
        substd-clcₐ :
          CollapsedCtcs m (cκsubst cκₐ (ClpCtcSpace.cκ ∘ σcls))
                          (reverse (sκssubst sκsₐ (ClpCtcSpace.sκs ∘ σcls)))
        substd-clcₐ rewrite sκssubst-reverse-comm sκsₐ (ClpCtcSpace.sκs ∘ σcls) =
          clcsubst-neg clcₐ pmκₐ σcls σp
  clcsubst-pos (μ/clc_ {sκs = sκs} clc) (μ/p pmκ) σcls σp
    rewrite sκssubst-μ/c-comm sκs (ClpCtcSpace.sκs ∘ σcls)
    = μ/clc (clcsubst-pos clc pmκ (clsext σcls) (pmκext σp))


  clcsubst-neg : ∀ {m Δ Δ′ δ δ′ τ} →
    {σ : tt ∈ Δ → TyN Δ′} →
    {cκ : SECtcN Δ τ} →
    {rev-sκs : Vec (SCtc1N Δ τ) m} →
    CollapsedCtcs m cκ rev-sκs →
    SECtcSigned neg δ cκ →
    (σcls : (a : tt ∈ Δ) → ClpCtcSpace m (ListAll.lookup δ a) (σ a)) →
    (σp : (a : tt ∈ Δ) → SECtcSigned (ListAll.lookup δ a) δ′ (ClpCtcSpace.cκ (σcls a))) →
    CollapsedCtcs m (cκsubst cκ (ClpCtcSpace.cκ ∘ σcls))
                    (sκssubst rev-sκs (reverse ∘ ClpCtcSpace.sκs ∘ σcls))
  clcsubst-neg {rev-sκs = rev-sκs} (` a) (var/p .a lookup-eq) σcls σp
    rewrite sκssubst-a-comm a rev-sκs (reverse ∘ ClpCtcSpace.sκs ∘ σcls)
          | cong (λ ± → signed-reverse ± (ClpCtcSpace.sκs (σcls a))) lookup-eq
    = ClpCtcSpace.clc (σcls a)
  clcsubst-neg 1/clc pmκ σcls σp = 1/clc
  clcsubst-neg (flat/clc {sκs = sκs} clp-preds) pmκ σcls σp =
    flat/clc (clpsubst (reverse ∘ ClpCtcSpace.sκs ∘ σcls) clp-preds)
  clcsubst-neg (_*/clc_ {sκs₁ = sκs₁} {sκs₂ = sκs₂} clc₁ clc₂) (pmκ₁ */p pmκ₂) σcls σp
    rewrite sκssubst-*/c-comm sκs₁ sκs₂ (reverse ∘ ClpCtcSpace.sκs ∘ σcls)
    = (clcsubst-neg clc₁ pmκ₁ σcls σp) */clc (clcsubst-neg clc₂ pmκ₂ σcls σp)
  clcsubst-neg (_+/clc_ {sκs₁ = sκs₁} {sκs₂ = sκs₂} clc₁ clc₂) (pmκ₁ +/p pmκ₂) σcls σp
    rewrite sκssubst-+/c-comm sκs₁ sκs₂ (reverse ∘ ClpCtcSpace.sκs ∘ σcls)
    = (clcsubst-neg clc₁ pmκ₁ σcls σp) +/clc (clcsubst-neg clc₂ pmκ₂ σcls σp)
  clcsubst-neg (box/clc {sκs = sκs} clc) (box/p pmκ) σcls σp
    rewrite sκssubst-box/c-comm sκs (reverse ∘ ClpCtcSpace.sκs ∘ σcls)
    = box/clc (clcsubst-neg clc pmκ σcls σp)
  clcsubst-neg {m = m} {cκ = cκₐ →/cc cκᵣ}
    (_→/clc_ {sκsₐ = sκsₐ} {sκsᵣ = sκsᵣ} clcₐ clcᵣ) (pmκₐ →/p pmκᵣ) σcls σp
    rewrite sκssubst-→/c-comm sκsₐ sκsᵣ (reverse ∘ ClpCtcSpace.sκs ∘ σcls)
    = substd-clcₐ →/clc clcsubst-neg clcᵣ pmκᵣ σcls σp where
        substd-clcₐ :
          CollapsedCtcs m (cκsubst cκₐ (ClpCtcSpace.cκ ∘ σcls))
                          (reverse (sκssubst sκsₐ (reverse ∘ ClpCtcSpace.sκs ∘ σcls)))
        substd-clcₐ
          rewrite sκssubst-reverse-comm sκsₐ (reverse ∘ ClpCtcSpace.sκs ∘ σcls)
                | sκssubst-≗ (reverse sκsₐ) (Vec.reverse-involutive ∘ ClpCtcSpace.sκs ∘ σcls)
          = clcsubst-pos clcₐ pmκₐ σcls σp
  clcsubst-neg (μ/clc_ {sκs = sκs} clc) (μ/p pmκ) σcls σp
    rewrite sκssubst-μ/c-comm sκs (reverse ∘ ClpCtcSpace.sκs ∘ σcls)
          | sκssubst-≗ sκs (sym ∘ sκsext-reverse-comm (ClpCtcSpace.sκs ∘ σcls))
    = μ/clc (clcsubst-neg clc pmκ (clsext σcls) (pmκext σp))


clcsubst : ∀ {± m Δ Δ′ δ δ′ τ} →
  {σ : tt ∈ Δ → TyN Δ′} →
  {cκ : SECtcN Δ τ} →
  {sκs : Vec (SCtc1N Δ τ) m} →
  CollapsedCtcs m cκ (signed-reverse ± sκs) →
  SECtcSigned ± δ cκ →
  (σcls : (a : tt ∈ Δ) → ClpCtcSpace m (ListAll.lookup δ a) (σ a)) →
  (σp : (a : tt ∈ Δ) → SECtcSigned (ListAll.lookup δ a) δ′ (ClpCtcSpace.cκ (σcls a))) →
  CollapsedCtcs m (cκsubst cκ (ClpCtcSpace.cκ ∘ σcls))
                  (signed-reverse ± (sκssubst sκs (ClpCtcSpace.sκs ∘ σcls)))
clcsubst {pos} clc pmκ σcls σp =
  clcsubst-pos clc pmκ σcls σp
clcsubst {neg} {sκs = sκs} clc pmκ σcls σp
  rewrite sκssubst-reverse-comm sκs (ClpCtcSpace.sκs ∘ σcls)
  = clcsubst-neg clc pmκ σcls σp


clc0mapsto : ∀ {± m Δ δ τ cκ sκs} →
  CollapsedCtcs m {Δ} {τ} cκ (signed-reverse ± sκs) →
  (a : tt ∈ (tt ∷ Δ)) →
  CollapsedCtcs m
                (([cκ0↦ cκ ]) a)
                (signed-reverse (ListAll.lookup (± ∷ δ) a) (map (λ sκ → ([sκ0↦ sκ ]) a) sκs))
clc0mapsto {sκs = sκs} clc (here refl) rewrite Vec.map-id sκs = clc
clc0mapsto             clc (there x∈Δ) = ` x∈Δ

cls0mapsto [cls0↦_] : ∀ {± m Δ δ τ cκ sκs} →
  CollapsedCtcs m cκ (signed-reverse ± sκs) →
  (a : tt ∈ (tt ∷ Δ)) →
  ClpCtcSpace m (ListAll.lookup (± ∷ δ) a) ([t0↦ τ ] a)
cls0mapsto clc a = record { cκ = _; sκs = _; clc = clc0mapsto clc a }

[cls0↦_] = cls0mapsto




clc-flat-preds : ∀ {m Δ cκ sκs} →
  CollapsedCtcs m {Δ} {`ℕ} cκ sκs →
  CollapsedPreds [] (flat/cc-preds cκ) sκs
clc-flat-preds (flat/clc clp-preds) = clp-preds

clc-*₁ : ∀ {m Δ τ₁ τ₂ cκ sκs} →
  CollapsedCtcs m {Δ} {τ₁ `* τ₂} cκ sκs →
  CollapsedCtcs m (*/cc-cκ₁ cκ) (map */c-sκ₁ sκs)
clc-*₁ (_*/clc_ {sκs₁ = sκs₁} {sκs₂ = sκs₂} clc₁ clc₂)
  rewrite */c-sκ₁-cancel sκs₁ sκs₂ = clc₁

clc-*₂ : ∀ {m Δ τ₁ τ₂ cκ sκs} →
  CollapsedCtcs m {Δ} {τ₁ `* τ₂} cκ sκs →
  CollapsedCtcs m (*/cc-cκ₂ cκ) (map */c-sκ₂ sκs)
clc-*₂ (_*/clc_ {sκs₁ = sκs₁} {sκs₂ = sκs₂} clc₁ clc₂)
  rewrite */c-sκ₂-cancel sκs₁ sκs₂ = clc₂

clc-+₁ : ∀ {m Δ τ₁ τ₂ cκ sκs} →
  CollapsedCtcs m {Δ} {τ₁ `+ τ₂} cκ sκs →
  CollapsedCtcs m (+/cc-cκ₁ cκ) (map +/c-sκ₁ sκs)
clc-+₁ (_+/clc_ {sκs₁ = sκs₁} {sκs₂ = sκs₂} clc₁ clc₂)
  rewrite +/c-sκ₁-cancel sκs₁ sκs₂ = clc₁

clc-+₂ : ∀ {m Δ τ₁ τ₂ cκ sκs} →
  CollapsedCtcs m {Δ} {τ₁ `+ τ₂} cκ sκs →
  CollapsedCtcs m (+/cc-cκ₂ cκ) (map +/c-sκ₂ sκs)
clc-+₂ (_+/clc_ {sκs₁ = sκs₁} {sκs₂ = sκs₂} clc₁ clc₂)
  rewrite +/c-sκ₂-cancel sκs₁ sκs₂ = clc₂

clc-box : ∀ {m Δ τ cκ sκs} →
  CollapsedCtcs m {Δ} {Box τ} cκ sκs →
  CollapsedCtcs m (box/cc-cκ cκ) (map box/c-sκ sκs)
clc-box (box/clc {sκs = sκs} clc)
  rewrite box/c-sκ-cancel sκs = clc

clc-dom : ∀ {m Δ τₐ τᵣ cκ sκs} →
  CollapsedCtcs m {Δ} {τₐ `→ τᵣ} cκ sκs →
  CollapsedCtcs m (→/cc-dom-cκ cκ) (reverse (map →/c-dom-sκ sκs))
clc-dom (_→/clc_ {sκsₐ = sκsₐ} {sκsᵣ = sκsᵣ} clcₐ clcᵣ)
  rewrite →/c-dom-sκ-cancel sκsₐ sκsᵣ = clcₐ

clc-rng : ∀ {m Δ τₐ τᵣ cκ sκs} →
  CollapsedCtcs m {Δ} {τₐ `→ τᵣ} cκ sκs →
  CollapsedCtcs m (→/cc-rng-cκ cκ) (map →/c-rng-sκ sκs)
clc-rng (_→/clc_ {sκsₐ = sκsₐ} {sκsᵣ = sκsᵣ} clcₐ clcᵣ)
  rewrite →/c-rng-sκ-cancel sκsₐ sκsᵣ = clcᵣ

clc-μ-pos : ∀ {m Δ δ τ cκ sκs} →
  SECtcSigned {Δ} pos δ cκ →
  CollapsedCtcs m {Δ} {μ τ} cκ sκs →
  CollapsedCtcs m (μ/cc-cκ cκ) (map μ/c-sκ sκs)
clc-μ-pos {cκ = μ/cc cκ} (μ/p pmκ) (μ/clc_ {sκs = sκs} clc)
  rewrite μ/c-sκ-cancel sκs
        | sκssubst-map (sκ0mapsto ∘ μ/c_) sκs
        | sκssubst-≗ sκs (λ x → Vec.map-∘ (λ sκ → ([sκ0↦ sκ ]) x) μ/c_ sκs)
  = clcsubst clc pmκ [cls0↦ μ/clc clc ] [pmκ0↦ μ/p pmκ ]
