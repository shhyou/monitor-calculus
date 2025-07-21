{-# OPTIONS --without-K --safe #-}

open import Annotation.Language

module Contract.Base (Label : Set) (𝒜 : AnnTerm) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; _++_; map; reverse)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Contract.Common Label

open AnnTerm 𝒜 using (Ann; State)

import TransitionRelationUtil
private
  variable
    Δ Δ′ : TCtxt
    τ τ₁ τ₂ τₐ τᵣ : TyN Δ
  module TR = TransitionRelationUtil State

-- Sharing the contract definitions trips the typecheck into an infinite eloop
data SCtc1N : (Δ : TCtxt) → TyN Δ → Set where
  `_    : (a : tt ∈ Δ) → SCtc1N Δ (` a)
  1/c   : SCtc1N Δ `1
  flat  : (l : Label) → (e : Ann ∣ (`ℕ ∷ []) ⊢ `ℕ) → SCtc1N Δ `ℕ
  _*/c_ : SCtc1N Δ τ₁ → SCtc1N Δ τ₂ → SCtc1N Δ (τ₁ `* τ₂)
  _+/c_ : SCtc1N Δ τ₁ → SCtc1N Δ τ₂ → SCtc1N Δ (τ₁ `+ τ₂)
  box/c : SCtc1N Δ τ → SCtc1N Δ (Box τ)
  _→/c_ : SCtc1N Δ τₐ → SCtc1N Δ τᵣ → SCtc1N Δ (τₐ `→ τᵣ)
  μ/c_  : SCtc1N (tt ∷ Δ) τ → SCtc1N Δ (μ τ)

sκflat-change-variable : SCtc1N Δ `ℕ → SCtc1N Δ′ `ℕ
sκflat-change-variable (flat l e) = flat l e

sκrename :
  SCtc1N Δ τ →
  (ren : tt ∈ Δ → tt ∈ Δ′) →
  SCtc1N Δ′ (trename τ ren)
sκrename (` a)           ren = ` ren a
sκrename 1/c             ren = 1/c
sκrename (flat l e)      ren = flat l e
sκrename (κ₁ */c κ₂)     ren = sκrename κ₁ ren */c sκrename κ₂ ren
sκrename (κ₁ +/c κ₂)     ren = sκrename κ₁ ren +/c sκrename κ₂ ren
sκrename (box/c κ)       ren = box/c (sκrename κ ren)
sκrename (κₐ →/c κᵣ)     ren = sκrename κₐ ren →/c sκrename κᵣ ren
sκrename (μ/c κ)         ren = μ/c (sκrename κ (pext ren))

sκext :
  {σ : tt ∈ Δ → TyN Δ′} →
  (σκ : (a : tt ∈ Δ) → SCtc1N Δ′ (σ a)) →
  (a : tt ∈ (tt ∷ Δ)) → SCtc1N (tt ∷ Δ′) (text σ a)
sκext σκ (here refl) = ` here refl
sκext σκ (there x∈Δ) = sκrename (σκ x∈Δ) there

sκsubst : ∀ {Δ Δ′ τ} →
  {σ : tt ∈ Δ → TyN Δ′} →
  SCtc1N Δ τ →
  (σκ : (a : tt ∈ Δ) → SCtc1N Δ′ (σ a)) →
  SCtc1N Δ′ (tsubst τ σ)
sκsubst (` a)           σκ = σκ a
sκsubst 1/c             σκ = 1/c
sκsubst (flat l e)      σκ = flat l e
sκsubst (κ₁ */c κ₂)     σκ = sκsubst κ₁ σκ */c sκsubst κ₂ σκ
sκsubst (κ₁ +/c κ₂)     σκ = sκsubst κ₁ σκ +/c sκsubst κ₂ σκ
sκsubst (box/c κ)       σκ = box/c (sκsubst κ σκ)
sκsubst (κₐ →/c κᵣ)     σκ = sκsubst κₐ σκ →/c sκsubst κᵣ σκ
sκsubst (μ/c κ)         σκ = μ/c (sκsubst κ (sκext σκ))

sκ0mapsto [sκ0↦_] : SCtc1N Δ τ → (a : tt ∈ (tt ∷ Δ)) → SCtc1N Δ ([t0↦ τ ] a)
sκ0mapsto κ (here refl) = κ
sκ0mapsto κ (there x∈Δ) = ` x∈Δ

[sκ0↦_] = sκ0mapsto

sκext-≗ :
  {σ : (a : tt ∈ Δ) → TyN Δ′} →
  {σκ σκ′ : (a : tt ∈ Δ) → SCtc1N Δ′ (σ a)} →
  (eq : (a : tt ∈ Δ) → σκ a ≡ σκ′ a) →
  (a : tt ∈ (tt ∷ Δ)) → sκext σκ a ≡ sκext σκ′ a
sκext-≗ eq (here refl) = refl
sκext-≗ eq (there x∈Δ) = cong (λ sκ → sκrename sκ there) (eq x∈Δ)

sκsubst-≗ :
  {σ : (a : tt ∈ Δ) → TyN Δ′} →
  (sκ : SCtc1N Δ τ) →
  {σκ σκ′ : (a : tt ∈ Δ) → SCtc1N Δ′ (σ a)} →
  (eq : (a : tt ∈ Δ) → σκ a ≡ σκ′ a) →
  sκsubst sκ σκ ≡ sκsubst sκ σκ′
sκsubst-≗ (` a)         eq = eq a
sκsubst-≗ 1/c           eq = refl
sκsubst-≗ (flat l e)    eq = refl
sκsubst-≗ (sκ₁ */c sκ₂) eq rewrite sκsubst-≗ sκ₁ eq | sκsubst-≗ sκ₂ eq = refl
sκsubst-≗ (sκ₁ +/c sκ₂) eq rewrite sκsubst-≗ sκ₁ eq | sκsubst-≗ sκ₂ eq = refl
sκsubst-≗ (box/c sκ)    eq = cong box/c (sκsubst-≗ sκ eq)
sκsubst-≗ (sκₐ →/c sκᵣ) eq rewrite sκsubst-≗ sκₐ eq | sκsubst-≗ sκᵣ eq = refl
sκsubst-≗ (μ/c sκ)      eq = cong μ/c_ (sκsubst-≗ sκ (sκext-≗ eq))

flat-pred : SCtc1N Δ `ℕ → Ann ∣ `ℕ ∷ [] ⊢ `ℕ
flat-pred (flat l e) = e

flat-pred-change-variable :
  ∀ sκ → flat-pred sκ ≡ flat-pred (sκflat-change-variable {Δ} {Δ′} sκ)
flat-pred-change-variable (flat l e) = refl

*/c-sκ₁ : SCtc1N Δ (τ₁ `* τ₂) → SCtc1N Δ τ₁
*/c-sκ₁ (κ₁ */c κ₂) = κ₁

*/c-sκ₂ : SCtc1N Δ (τ₁ `* τ₂) → SCtc1N Δ τ₂
*/c-sκ₂ (κ₁ */c κ₂) = κ₂

+/c-sκ₁ : SCtc1N Δ (τ₁ `+ τ₂) → SCtc1N Δ τ₁
+/c-sκ₁ (κ₁ +/c κ₂) = κ₁

+/c-sκ₂ : SCtc1N Δ (τ₁ `+ τ₂) → SCtc1N Δ τ₂
+/c-sκ₂ (κ₁ +/c κ₂) = κ₂

box/c-sκ : SCtc1N Δ (Box τ) → SCtc1N Δ τ
box/c-sκ (box/c κ) = κ

→/c-dom-sκ : SCtc1N Δ (τₐ `→ τᵣ) → SCtc1N Δ τₐ
→/c-dom-sκ (κₐ →/c κᵣ) = κₐ

→/c-rng-sκ : SCtc1N Δ (τₐ `→ τᵣ) → SCtc1N Δ τᵣ
→/c-rng-sκ (κₐ →/c κᵣ) = κᵣ

μ/c-sκ : SCtc1N Δ (μ τ) → SCtc1N Δ (tsubst τ [t0↦ μ τ ])
μ/c-sκ (μ/c κ) = sκsubst κ [sκ0↦ μ/c κ ]

μ/c-sκ′ : SCtc1N Δ (μ τ) → SCtc1N (tt ∷ Δ) τ
μ/c-sκ′ (μ/c κ) = κ

SCtc1 : Ty → Set
SCtc1 τ = SCtc1N [] τ

𝒜sctc : AnnTerm
AnnTerm.Ann   𝒜sctc τ = List (SCtc1N [] τ)
AnnTerm.State 𝒜sctc   = Status

module _ (𝒜view : AnnTermView 𝒜 𝒜sctc) (𝒯 : AnnTransit 𝒜) where
  open AnnTermViewUtils 𝒜view

  checkNatSCtcs :
    List (SCtc1 `ℕ) →
    (v : Ann  ∣  [] ⊢ `ℕ) →
    State → State → Set
  checkNatSCtcs []        v = TR.id
  checkNatSCtcs (flat l e ∷ sκs) v =
    ( (guardState Ok  TR.∘  CheckNatPred getState putState (𝒯 ⊢_,_⟶*_,_) l e v) TR.⊎
      (λ s s′ → ∃ λ l → guardState (Err l) s s′)  ) TR.∘
    checkNatSCtcs sκs v

  fallthrough-check-nat-sctcs : ∀ {n l s} →
    getATState 𝒜view s ≡ Err l →
    (sκs : List (SCtc1N [] `ℕ)) →
    checkNatSCtcs sκs n s s
  fallthrough-check-nat-sctcs s-eq [] = refl
  fallthrough-check-nat-sctcs s-eq (flat l′ ep ∷ sκs) =
    _ , inj₂ (_ , s-eq ,′ refl) ,′ fallthrough-check-nat-sctcs s-eq sκs

  𝒯sctc : AnnTransit 𝒜
  𝒯sctc `R-cross-unit (_ , refl) (ϑ , tt) ψ ψ′ =
    guardState Ok
  𝒯sctc `R-cross-nat (_ , refl) (ϑ , isval) ψ ψ′ =
    guardState Ok  TR.∘
    checkNatSCtcs (getAnn(ψ(here refl))) (ϑ(here refl))
  𝒯sctc `R-cross-cons (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁ , isval₂) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ sκs , sκs₁ , sκs₂ ←
                                       ψ(here refl) , ψ′(here refl) , ψ′(there (here refl)) ]
                                sκs₁ ≡ map */c-sκ₁ sκs ×
                                sκs₂ ≡ map */c-sκ₂ sκs ]
  𝒯sctc `R-cross-inl (_ , (τ₁ , τ₂) , refl) (ϑ , isval₁) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ sκs , sκs₁ ← ψ(here refl) , ψ′(here refl) ]
                                sκs₁ ≡ map +/c-sκ₁ sκs ]
  𝒯sctc `R-cross-inr (_ , (τ₁ , τ₂) , refl) (ϑ , isval₂) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ sκs , sκs₂ ← ψ(here refl) , ψ′(here refl) ]
                                sκs₂ ≡ map +/c-sκ₂ sκs ]
  𝒯sctc `R-cross-roll (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ sκs , sκs′ ← ψ(here refl) , ψ′(here refl) ]
                                sκs′ ≡ map μ/c-sκ sκs ]
  𝒯sctc `R-cross-box (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ sκs , sκs′ ← ψ(here refl) , ψ′(here refl) ]
                                sκs′ ≡ sκs ]
  𝒯sctc `R-cross-lam (_ , (τₐ , τᵣ) , refl) (ϑ , tt) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ sκs , sκs′ ← ψ(here refl) , ψ′(here refl) ]
                                sκs′ ≡ sκs ]
  𝒯sctc `R-merge-box (_ , τ′ , refl) (ϑ , isval) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ sκs , sκs′ , sκs″ ←
                                       ψ(here refl) , ψ(there (here refl)) , ψ′(here refl) ]
                                sκs″ ≡ sκs′ ++ sκs ]
  𝒯sctc `R-merge-lam (_ , (τₐ , τᵣ) , refl) (ϑ , tt) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ sκs , sκs′ , sκs″ ←
                                       ψ(here refl) , ψ(there (here refl)) , ψ′(here refl) ]
                                sκs″ ≡ sκs′ ++ sκs ]
  𝒯sctc `R-proxy-unbox (τ , tt) (ϑ , isval) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ sκs , sκs′ ← ψ(here refl) , ψ′(here refl) ]
                                sκs′ ≡ map box/c-sκ sκs ]
  𝒯sctc `R-proxy-β (τᵣ , τₐ) (ϑ , isval) ψ ψ′ =
    guardState Ok  TR.∩  TR.[ getAnn[ sκs , sκsₐ , sκsᵣ ←
                                       ψ(here refl) , ψ′(here refl) , ψ′(there (here refl)) ]
                                sκsₐ ≡ reverse (map →/c-dom-sκ sκs) ×
                                sκsᵣ ≡ map →/c-rng-sκ sκs ]

  data CheckingSteps {n} (iv : Ann ∣ n isvalof `ℕ) (s s′ : State) (eκ : Ann ∣ [] ⊢ `ℕ) :
    (sκs : List (SCtc1N [] `ℕ)) → Set where
      [_,_]ᶜ : ∀ {l ep} →
        (steps : 𝒯 ⊢ s , esubst ep [x0↦ n ] ⟶* s′ , eκ) →
        getATState 𝒜view s′ ≡ Ok →
        CheckingSteps iv s s′ eκ (flat l ep ∷ [])

      ⟨_,_⟩∷_ : ∀ {l ep sκs s₁} →
        (ok-steps : CheckNatPred (getATState 𝒜view) (putATState 𝒜view) (𝒯 ⊢_,_⟶*_,_) l ep n s s₁) →
        getATState 𝒜view s₁ ≡ Ok →
        CheckingSteps iv s₁ s′ eκ sκs →
        CheckingSteps iv s  s′ eκ (flat l ep ∷ sκs)

  next-checking-steps : ∀ {n m s s′ sκs} {nval : Ann ∣ n isvalof `ℕ} →
    Ann ∣ m isvalof `ℕ →
    CheckingSteps nval s s′ (`s m) sκs →
    (sκ : SCtc1N [] `ℕ) →
    ∃[ eκ ] CheckingSteps nval s s′ eκ (sκs ++ sκ ∷ [])
  next-checking-steps iv [ steps , s′-ok ]ᶜ (flat l e) =
    _ , ⟨ NP-acc iv steps s′-ok , s′-ok ⟩∷ [ R-refl , s′-ok ]ᶜ
  next-checking-steps iv (⟨ ok-steps , s₁-ok ⟩∷ chk-steps) sκ =
    _ , ⟨ ok-steps , s₁-ok ⟩∷ proj₂ (next-checking-steps iv chk-steps sκ)

  step-check-nat-sctcs : ∀ {n eκ eκ′ s s′ s″ sκs} {nval : Ann ∣ n isvalof `ℕ} →
    𝒯 ⊢ s′ , eκ ⟶ s″ , eκ′ →
    getATState 𝒜view s″ ≡ Ok →
    CheckingSteps nval s s′ eκ sκs →
    CheckingSteps nval s s″ eκ′ sκs
  step-check-nat-sctcs step s″-ok [ steps , s′-ok ]ᶜ = [ R-step steps step , s″-ok ]ᶜ
  step-check-nat-sctcs step s″-ok (⟨ ok-steps , s₁-ok ⟩∷ chk-steps) =
    ⟨ ok-steps , s₁-ok ⟩∷ step-check-nat-sctcs step s″-ok chk-steps

  accept-check-nat-sctcs : ∀ {n m sκs s s′} {nval : Ann ∣ n isvalof `ℕ} →
    getATState 𝒜view s ≡ Ok →
    CheckingSteps nval s s′ (`s m) sκs →
    Ann ∣ m isvalof `ℕ →
    getATState 𝒜view s′ ≡ Ok × checkNatSCtcs sκs n s s′
  accept-check-nat-sctcs s-ok [ steps , s′-ok ]ᶜ iv =
    s′-ok ,′
    (_ , inj₁ (_ , (s-ok ,′ refl) ,′ NP-acc iv steps s′-ok) ,′ refl)
  accept-check-nat-sctcs s-ok (⟨ ok-steps , s₁-ok ⟩∷ chk-steps) iv =
    proj₁ s′-ok,check-nat-sctcs ,′
    (_ , inj₁ (_ , (s-ok ,′ refl) ,′ ok-steps) ,′ proj₂ s′-ok,check-nat-sctcs)
    where s′-ok,check-nat-sctcs = accept-check-nat-sctcs s₁-ok chk-steps iv

  reject-check-nat-sctcs : ∀ {n s s′ sκs-init} {nval : Ann ∣ n isvalof `ℕ} →
    (sκs : List (SCtc1N [] `ℕ)) →
    getATState 𝒜view s ≡ Ok →
    CheckingSteps nval s s′ `z sκs-init →
    ∃[ l ] checkNatSCtcs (sκs-init ++ sκs) n s (putATState 𝒜view (Err l) s′)
  reject-check-nat-sctcs {s′ = s′} {sκs-init = flat l ep ∷ []} sκs s-ok [ steps , s′-ok ]ᶜ =
    l , _ ,
    inj₁ (_ , (s-ok ,′ refl) ,′
    NP-rej steps s′-ok refl) ,′
    fallthrough-check-nat-sctcs (AnnTermView.put-get 𝒜view s′ (Err l)) sκs
  reject-check-nat-sctcs sκs s-ok (⟨ ok-steps , s₁-ok ⟩∷ chk-steps) =
    _ , _ ,
    inj₁ (_ , (s-ok ,′ refl) ,′ ok-steps) ,′
    proj₂ (reject-check-nat-sctcs sκs s₁-ok chk-steps)

  error-check-nat-sctcs : ∀ {l n eκ eκ′ s s′ s″ sκs-init} {nval : Ann ∣ n isvalof `ℕ} →
    (sκs : List (SCtc1N [] `ℕ)) →
    getATState 𝒜view s ≡ Ok →
    CheckingSteps nval s s′ eκ sκs-init →
    𝒯 ⊢ s′ , eκ ⟶ s″ , eκ′ →
    getATState 𝒜view s″ ≡ Err l →
    checkNatSCtcs (sκs-init ++ sκs) n s s″
  error-check-nat-sctcs {l = l} sκs s-ok [ steps , s′-ok ]ᶜ err-step s″-err =
    _ ,
    inj₁ (_ , (s-ok ,′ refl) ,′
    NP-err (R-step steps err-step) l s″-err) ,′
    fallthrough-check-nat-sctcs s″-err sκs
  error-check-nat-sctcs sκs s-ok (⟨ ok-steps , s₁-ok ⟩∷ chk-steps) err-step s″-err =
    _ ,
    inj₁ (_ , (s-ok ,′ refl) ,′ ok-steps) ,′
    error-check-nat-sctcs sκs s₁-ok chk-steps err-step s″-err
