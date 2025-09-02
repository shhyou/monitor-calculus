{-# OPTIONS --without-K --safe #-}

module Blame.Progress (Label : Set) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; trans; sym; subst; cong; module ≡-Reasoning)

open import Data.Unit.Base as Unit using (⊤; tt) -- needed for the number typeclass
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; [_]; _++_; reverse; map)
import Data.List.Properties as List
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as ListAll
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)

open import Function.Base using (_∘_)

open ≡-Reasoning using (begin_; _∎; step-≡-⟨; step-≡-⟩; step-≡-∣)

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import OpSemantics.TypeSafety
open import Annotation.Language
open import Annotation.Invariant
open import Annotation.Soundness

𝒜blame-sctc : AnnTerm

open import Blame.Base Label

open import Contract.Common Label
open import Contract.Base Label 𝒜blame-sctc
open import Contract.Satisfaction Label 𝒜blame-sctc

AnnTerm.Ann   𝒜blame-sctc τ = (Label × Label) × List (Blame × SCtc1N [] τ)
AnnTerm.State 𝒜blame-sctc   = Status

open AnnBlameContractLang 𝒜blame-sctc hiding (𝒜blame-sctc)
open import Blame.Ownership Label 𝒜blame-sctc-owner-view 𝒜blame-sctc-blame-view

open AnnTerm 𝒜blame-sctc
open AnnRule 𝒜blame-sctc

infix 6 ∎_
infixl 5 _►_checking⟨_∣_⟩
infixl 5 _∷ᶠ_

data Frames : Set where
  ∎_ : ∀ {τ} → (e : Ann ∣ [] ⊢ τ) → Frames
  _►_checking⟨_∣_⟩ :
    Frames →
    (eᵣ : Ann ∣ [] ⊢ `ℕ) →
    (eκ : Ann ∣ [] ⊢ `ℕ) →
    (bsκs : List (Blame × SCtc1N [] `ℕ)) →
    Frames

record Frame (j : ℕ) {τ} e eᵣ bsκs eκ : Set where
  constructor mkFrame
  no-eta-equality; pattern
  field
    pending : PendingStep (R-cross-nat Ann) eᵣ
    bsκs-init : List (Blame × SCtc1N [] `ℕ)
    redex : Ann ∣ e ⦂ τ ▷ eᵣ ⦂ `ℕ
    {bsκs-all} : List (Blame × SCtc1N [] `ℕ)
    {n} : Ann ∣ [] ⊢ `ℕ
    {ℓₙ ℓₚ} : Label
    redex-intr : ℐowner (suc j) ⊨[ ℓₙ ] eᵣ
    redex-eq : eᵣ ≡ B# ((ℓₙ ,′ ℓₚ) ,′ bsκs-all) ⟪ n ⟫
    nval : Ann ∣ n isvalof `ℕ
    split-eq : bsκs-all ≡ bsκs-init ++ bsκs
    chk-steps : CheckingSteps 𝒜sctc-view (𝒯 j) nval Ok Ok eκ (map proj₂ bsκs-init)

accept-checking-frame : ∀ {j τ} {e : Ann ∣ [] ⊢ τ} {m eᵣ} →
  Ann ∣ m isvalof `ℕ →
  (frame : Frame j e eᵣ [] (`s m)) →
  ∃[ e′ ] 𝒯 (suc j) ⊢ Ok , e ⟶ Ok , e′
accept-checking-frame {j = j}
  iv
  (mkFrame  pending@(mkPendingStep refl termEnv (mkTerm ψ₁ refl) iv₁)
            bsκs-init ec ⊨eᵣ refl nval split-eq chk-steps)
  = _ ,
    R-bdr `R-cross-nat Ok Ok
            (proj₂ (plug-∃ ec (Pending⇒Step pending
                                            (λ ())
                                            (_ ,′ tt ,′ Ok , (refl ,′ refl) ,′ subst-check-nat-sctcs))))

  where
    acc-checkNatSCtcs = proj₂ (accept-check-nat-sctcs 𝒜sctc-view (𝒯 j) refl chk-steps iv)

    check-nat-sctcs-ty : List (Blame × SCtc1N [] `ℕ) → Set
    check-nat-sctcs-ty bsκs =
      checkNatSCtcs 𝒜sctc-view (𝒯 j) (map proj₂ bsκs) (termEnv(here refl)) Ok Ok

    bsκs-eq : bsκs-init ≡ proj₂(ψ₁(here refl))
    bsκs-eq = sym (trans split-eq (List.++-identityʳ bsκs-init))

    subst-check-nat-sctcs = subst check-nat-sctcs-ty bsκs-eq acc-checkNatSCtcs

reject-checking-frame : ∀ {j τ} {e : Ann ∣ [] ⊢ τ} {bsκs eᵣ} →
  (frame : Frame j e eᵣ bsκs `z) →
  ∃[ l ] ∃[ e′ ] 𝒯 (suc j) ⊢ Ok , e ⟶ Err l , e′
reject-checking-frame {j = j} {bsκs = bsκs}
  (mkFrame  pending@(mkPendingStep refl termEnv (mkTerm ψ₁ refl) iv₁)
            bsκs-init ec ⊨eᵣ refl nval split-eq chk-steps)
  = _ , _ ,
    R-bdr `R-cross-nat Ok (Err (proj₁ l,checkNatSCtcs))
            (proj₂ (plug-∃ ec (Pending⇒Step pending
                                            (λ ())
                                            (_ ,′ tt ,′ Ok , (refl ,′ refl) ,′ subst-check-nat-sctcs))))

  where
    l,checkNatSCtcs = reject-check-nat-sctcs 𝒜sctc-view (𝒯 j) (map proj₂ bsκs) refl chk-steps

    check-nat-sctcs-ty : List (SCtc1N [] `ℕ) → Set
    check-nat-sctcs-ty sκs =
      checkNatSCtcs 𝒜sctc-view (𝒯 j) sκs (termEnv(here refl)) Ok (Err (proj₁ l,checkNatSCtcs))

    bsκs-eq : map proj₂ (proj₂(ψ₁(here refl))) ≡ map proj₂ bsκs-init ++ map proj₂ bsκs
    bsκs-eq = trans (cong (map proj₂) split-eq) (List.map-++ proj₂ bsκs-init bsκs)

    subst-check-nat-sctcs = subst check-nat-sctcs-ty (sym bsκs-eq) (proj₂ l,checkNatSCtcs)

error-checking-frame : ∀ {j τ} {e : Ann ∣ [] ⊢ τ} {eᵣ eκ eκ′ bsκs l} →
  𝒯 j ⊢ Ok , eκ ⟶ Err l , eκ′ →
  (frame : Frame j e eᵣ bsκs eκ) →
  ∃[ e′ ] 𝒯 (suc j) ⊢ Ok , e ⟶ Err l , e′
error-checking-frame {j = j} {bsκs = bsκs} {l = l}
  err-step
  (mkFrame  pending@(mkPendingStep refl termEnv (mkTerm ψ₁ refl) iv₁)
            bsκs-init ec ⊨eᵣ refl nval split-eq chk-steps)
  = _ ,
    R-bdr `R-cross-nat Ok (Err l)
            (proj₂ (plug-∃ ec (Pending⇒Step pending
                                            (λ ())
                                            (_ ,′ tt ,′ Ok , (refl ,′ refl) ,′ subst-check-nat-sctcs))))
  where
    err-checkNatSCtcs = error-check-nat-sctcs 𝒜sctc-view (𝒯 j) (map proj₂ bsκs) refl chk-steps err-step refl

    check-nat-sctcs-ty : List (SCtc1N [] `ℕ) → Set
    check-nat-sctcs-ty sκs =
      checkNatSCtcs 𝒜sctc-view (𝒯 j) sκs (termEnv(here refl)) Ok (Err l)

    bsκs-eq : map proj₂ (proj₂(ψ₁(here refl))) ≡ map proj₂ bsκs-init ++ map proj₂ bsκs
    bsκs-eq = trans (cong (map proj₂) split-eq) (List.map-++ proj₂ bsκs-init bsκs)

    subst-check-nat-sctcs = subst check-nat-sctcs-ty (sym bsκs-eq) err-checkNatSCtcs


nval-sat : ∀ {𝒜 𝒯 n} (ℐ : AnnInvr {𝒜} 𝒯) {ix} →
  (nval : ATAnn 𝒜 ∣ n isvalof `ℕ) →
  ℐ ⊨[ ix ] n
nval-sat ℐ z/v        = `z
nval-sat ℐ (s/v nval) = `s (nval-sat ℐ nval)

-- Note: this can be partially generalized to other monotonic and sound interpretations ℐ
lookup-all-sctc-sat : ∀ {eκ n} →
  (i : ℕ) →
  {bsκs : List (Blame × SCtc1N [] `ℕ)} →
  {nval : Ann ∣ n isvalof `ℕ} →
  All (SCtcSat′ (ℐowner i) ∘ proj₂) bsκs →
  CheckingSteps 𝒜sctc-view (𝒯 i) nval Ok Ok eκ (map proj₂ bsκs) →
  ∃[ ℓⱼ ] ℐowner i ⊨[ ℓⱼ ] eκ
lookup-all-sctc-sat i {(b , sκ) ∷ []} {nval} ((ℓⱼ , flat/s ⊨ep) ∷ []) [ steps , refl ]ᶜ =
  ℓⱼ ,
  soundness*  (ℐowner i) (ℐowner-monotonic i) (ℐowner-sound i)
              steps
              tt
              (isubst ⊨ep [i0↦ nval-sat (ℐowner i) nval ])
lookup-all-sctc-sat i {(b , sκ) ∷ bsκs@(_ ∷ _)} (j-κsat ∷ j-κsats) (⟨ ok-steps , refl ⟩∷ chk-steps) =
  lookup-all-sctc-sat i j-κsats chk-steps


mutual
  data BSCtcFrames : ℕ → ℕ → Frames → Set where
    [_,_]ᶠ : ∀ {i j τ} →
      (j-eq : i ≡ j) →
      (e : Ann ∣ [] ⊢ τ) →
      BSCtcFrames i j (∎ e)
    _∷ᶠ_ : ∀ {τ i j evs eᵣ eκ₁ eκ bsκs} →
      (rest : BSCtcFramesRest {τ} i (suc j) evs eκ₁) →
      (frame : Frame j eκ₁ eᵣ bsκs eκ) →
      BSCtcFrames i j (evs ► eᵣ checking⟨ eκ ∣ bsκs ⟩)

  data BSCtcFramesRest : ∀ {τ} → ℕ → ℕ → Frames → Ann ∣ [] ⊢ τ → Set where
    one : ∀ {τ i j} {e : Ann ∣ [] ⊢ τ} →
      (frames : BSCtcFrames i j (∎ e)) →
      BSCtcFramesRest i j (∎ e) e

    more : ∀ {i j evs eᵣ eκ bsκs} →
      (frames : BSCtcFrames i j (evs ► eᵣ checking⟨ eκ ∣ bsκs ⟩)) →
      BSCtcFramesRest i j (evs ► eᵣ checking⟨ eκ ∣ bsκs ⟩) eκ

step-blame-sctc-frames : ∀ {i j evs eᵣ eκ eκ′ bsκs} →
  (step : 𝒯 j ⊢ Ok , eκ ⟶ Ok , eκ′) →
  BSCtcFrames i j (evs ► eᵣ checking⟨ eκ  ∣ bsκs ⟩) →
  BSCtcFrames i j (evs ► eᵣ checking⟨ eκ′ ∣ bsκs ⟩)
step-blame-sctc-frames {j = j} step (frames ∷ᶠ mkFrame pending bsκs-init ec ⊨eᵣ redex-eq nval split-eq chk-steps) =
  frames ∷ᶠ mkFrame pending bsκs-init ec ⊨eᵣ redex-eq nval split-eq stepped-chk-steps
  where stepped-chk-steps = step-check-nat-sctcs 𝒜sctc-view (𝒯 j) step refl chk-steps

next-blame-sctc-frames : ∀ {i j evs eᵣ m bsκ bsκs} →
  Ann ∣ m isvalof `ℕ →
  BSCtcFrames i j (evs ► eᵣ checking⟨ `s m ∣ bsκ ∷ bsκs ⟩) →
  ∃[ eκ ] BSCtcFrames i j (evs ► eᵣ checking⟨ eκ ∣ bsκs ⟩)
next-blame-sctc-frames {j = j} {bsκ = bsκ} {bsκs} iv
  (frames ∷ᶠ mkFrame pending bsκs-init ec ⊨eᵣ redex-eq nval split-eq chk-steps)
  rewrite sym (List.++-assoc bsκs-init [ bsκ ] bsκs)
  = _ , frames ∷ᶠ mkFrame pending (bsκs-init ++ [ bsκ ]) ec ⊨eᵣ redex-eq nval split-eq subst-chk-steps′
  where
    eκ,chk-steps′ = next-checking-steps 𝒜sctc-view (𝒯 j) iv chk-steps (proj₂ bsκ)

    checking-steps-ty : List (SCtc1N [] `ℕ) → Set
    checking-steps-ty sκs =
      CheckingSteps 𝒜sctc-view (𝒯 j) nval Ok Ok (proj₁ eκ,chk-steps′) sκs

    bsκs-eq : map proj₂ (bsκs-init ++ [ bsκ ]) ≡ map proj₂ bsκs-init ++ [ proj₂ bsκ ]
    bsκs-eq = List.map-++ proj₂ bsκs-init [ bsκ ]

    subst-chk-steps′ = subst checking-steps-ty (sym bsκs-eq) (proj₂ eκ,chk-steps′)


mutual
  data BSCtcProgress : ℕ → Frames → Set where
    BP-val : ∀ {i τ v} →
      (iv : Ann ∣ v isvalof τ) →
      BSCtcProgress (suc i) (∎ v)

    BP-err : ∀ {i τ e} →
      (ec : Ann ∣ e ⦂ τ ▷ (assert `z) ⦂ `1) →
      BSCtcProgress (suc i) (∎ e)

    BP-step : ∀ {i τ s′} {e e′ : Ann ∣ [] ⊢ τ} →
      𝒯 (suc i) ⊢ Ok , e ⟶ s′ , e′ →
      BSCtcProgress (suc i) (∎ e)

    BP-start-checking : ∀ {τ i} {e : Ann ∣ [] ⊢ τ} {e₁ bsκs eκ} →
      BSCtcFrames   (suc i) i (∎ e ► e₁ checking⟨ eκ ∣ bsκs ⟩) →
      BSCtcProgress (suc i)   (∎ e)

  data BSCtcBlames (l : Label) : ℕ → ℕ → Frames → Set where
    BB-blame : ∀ {τ i j} {e e′ : Ann ∣ [] ⊢ τ} →
      suc i ≡ j →
      𝒯 (suc i) ⊢ Ok , e ⟶ Err l , e′ →
      BSCtcBlames l (suc i) j (∎ e)

    BB-frame : ∀ {i j evs e eκ eκ′ bsκs} →
      BSCtcBlames l (suc i) (suc j) evs →
      𝒯 j ⊢ Ok , eκ ⟶ Err l , eκ′ →
      BSCtcBlames l (suc i) j (evs ► e checking⟨ eκ ∣ bsκs ⟩)

  data BSCtcCheckingProgress : ℕ → ℕ → Frames → Set where
    BCP-blame : ∀ {i j l evs e eκ bsκs} →
      BSCtcBlames         l (suc i) (suc j) evs →
      BSCtcCheckingProgress (suc i) j       (evs ► e checking⟨ eκ ∣ bsκs ⟩)

    BCP-finish-all-checking : ∀ {τ i} {e e′ : Ann ∣ [] ⊢ τ} {e₁ m} →
      (iv : Ann ∣ m isvalof `ℕ) →
      𝒯 (suc i) ⊢ Ok , e ⟶ Ok , e′ →
      BSCtcCheckingProgress (suc i) i (∎ e ► e₁ checking⟨ `s m ∣ [] ⟩)

    BCP-finish-one-checking : ∀ {i j evs e₁ e₂ eκ eκ′ m bsκs} →
      (iv : Ann ∣ m isvalof `ℕ) →
      𝒯 (suc j) ⊢ Ok , eκ ⟶ Ok , eκ′ →
      BSCtcFrames           (suc i) (suc j) (evs ► e₁ checking⟨ eκ′ ∣ bsκs ⟩) →
      BSCtcCheckingProgress (suc i) j       (evs ► e₁ checking⟨ eκ  ∣ bsκs ⟩ ► e₂ checking⟨ `s m ∣ [] ⟩)

    BCP-finish-one-sctc : ∀ {i j evs e eκ m sκ bsκs} →
      (iv : Ann ∣ m isvalof `ℕ) →
      BSCtcFrames           (suc i) j (evs ► e checking⟨ eκ   ∣ bsκs ⟩) →
      BSCtcCheckingProgress (suc i) j (evs ► e checking⟨ `s m ∣ sκ ∷ bsκs ⟩)

    BCP-step : ∀ {i j evs e eκ eκ′ bsκs} →
      𝒯 j ⊢ Ok , eκ ⟶ Ok , eκ′ →
      BSCtcFrames           (suc i) j (evs ► e checking⟨ eκ′ ∣ bsκs ⟩) →
      BSCtcCheckingProgress (suc i) j (evs ► e checking⟨ eκ  ∣ bsκs ⟩)

    BCP-err : ∀ {i j evs e eκ bsκs} →
      (ec : Ann ∣ eκ ⦂ `ℕ ▷ (assert `z) ⦂ `1) →
      BSCtcCheckingProgress (suc i) j (evs ► e checking⟨ eκ ∣ bsκs ⟩)

    BCP-start-new-checking : ∀ {i j evs e₁ e₂ eκ eκ₂ bsκs bsκs′} →
      BSCtcFrames           (suc i) j       (evs ► e₁ checking⟨ eκ ∣ bsκs ⟩ ► e₂ checking⟨ eκ₂ ∣ bsκs′ ⟩) →
      BSCtcCheckingProgress (suc i) (suc j) (evs ► e₁ checking⟨ eκ ∣ bsκs ⟩)

    BCP-pending : ∀ {i τ evs e₁ e₂ eκ bsκs} →
      (ec : Ann ∣ eκ ⦂ `ℕ ▷ e₂ ⦂ τ) →
      (tag : RuleTag) →
      (pending : PendingStep (AnnRules Ann tag) e₂) →
      BSCtcCheckingProgress (suc i) 0 (evs ► e₁ checking⟨ eκ ∣ bsκs ⟩)

  blame-sctc-progress : ∀ {τ} i {e : Ann ∣ [] ⊢ τ} {ℓ} →
    (⊨eown : ℐowner (suc i) ⊨[ ℓ ] e) →
    BSCtcProgress (suc i) (∎ e)
  blame-sctc-progress i {e = e} ⊨eown with progress Ok e
  ... | P-step step = BP-step (R-redex step)
  ... | P-err ec = BP-err ec
  ... | P-val iv = BP-val iv
  ... | P-pending ec tag pending with blame-sctc-pending-progress i ⊨eown ec tag pending
  ... | inj₁ (_ , step) = BP-step step
  ... | inj₂ (_ , _ , _ , frame) = BP-start-checking (one [ refl , e ]ᶠ ∷ᶠ frame)

  blame-sctc-blames : ∀ {i j l evs e eκ eκ′ bsκs} →
    𝒯 j ⊢ Ok , eκ ⟶ Err l , eκ′ →
    BSCtcFrames   (suc i) j (evs ► e checking⟨ eκ ∣ bsκs ⟩) →
    BSCtcBlames l (suc i) j (evs ► e checking⟨ eκ ∣ bsκs ⟩)
  blame-sctc-blames step (one [ refl , e ]ᶠ ∷ᶠ frame) =
    BB-frame (BB-blame refl (proj₂ (error-checking-frame step frame))) step
  blame-sctc-blames step (more frames ∷ᶠ frame) =
    BB-frame (blame-sctc-blames (proj₂ (error-checking-frame step frame)) frames) step

  blame-sctc-checking-progress : ∀ {i j eκ bsκs evs e} →
    BSCtcFrames           (suc i) j (evs ► e checking⟨ eκ ∣ bsκs ⟩) →
    BSCtcCheckingProgress (suc i) j (evs ► e checking⟨ eκ ∣ bsκs ⟩)
  blame-sctc-checking-progress {eκ = eκ} frames with progress Ok eκ
  blame-sctc-checking-progress frames                   | P-step step =
    BCP-step (R-redex step) (step-blame-sctc-frames (R-redex step) frames)
  blame-sctc-checking-progress frames                   | P-err ec = BCP-err ec
  blame-sctc-checking-progress {j = j} {eκ = eκ} frames | P-pending ec tag pending with j
  ... | zero     = BCP-pending ec tag pending
  ... | (suc j′)
    with  (f-rest ∷ᶠ frame@record { redex-intr = B/i ℓₙ ℓₚ ℓₙ◁ℓₚ (bs-own-eq , j-κsat) esat
                                  ; redex-eq = refl
                                  ; bsκs-init = bsκs-init
                                  ; split-eq = refl
                                  ; chk-steps = chk-steps }) ← frames
        | blame-sctc-pending-progress j′
            -- Here ,lookup-all-sctc-sat actually needs `esat : ℐowner ⊨ n` when enforcing the
            -- predicates but note that `esat` is satisfied under `ℐowner (suc (suc j′))` whereas
            -- the predicates actually need `ℐowner (suc j′)` since they are evaluated in
            -- one smaller nesting depth.
            --
            -- Although `ℐowner ⊨ n` always holds and hence does not matter, in general this would
            -- not be the case for higher-order functions, e.g., in the presence of dependent
            -- contracts. I think in that case `ℐowner` needs to be ‘downward closed’.
            (proj₂ (lookup-all-sctc-sat (suc j′) (ListAll.++⁻ˡ bsκs-init j-κsat) chk-steps))
            ec
            tag
            pending
  ... | inj₁ (_ , step) = BCP-step step (step-blame-sctc-frames step frames)
  ... | inj₂ (_ , _ , _ , frame) = BCP-start-new-checking (more frames ∷ᶠ frame)
  blame-sctc-checking-progress            (one [ refl , e ]ᶠ ∷ᶠ frame) | P-val z/v =
    BCP-blame (BB-blame refl (proj₂ (proj₂ (reject-checking-frame frame))))
  blame-sctc-checking-progress            (more frames  ∷ᶠ frame)      | P-val z/v =
    BCP-blame (blame-sctc-blames (proj₂ (proj₂ (reject-checking-frame frame))) frames)
  blame-sctc-checking-progress {bsκs = []} (one [ refl , e ]ᶠ ∷ᶠ frame) | P-val (s/v iv) =
    BCP-finish-all-checking iv (proj₂ (accept-checking-frame iv frame))
  blame-sctc-checking-progress {bsκs = []} (more frames ∷ᶠ frame)       | P-val (s/v iv) =
    BCP-finish-one-checking iv step (step-blame-sctc-frames step frames)
    where step = proj₂ (accept-checking-frame iv frame)
  blame-sctc-checking-progress {bsκs = (b , flat l ep) ∷ bsκs} (rest ∷ᶠ frame) | P-val (s/v iv) =
    BCP-finish-one-sctc iv (proj₂ (next-blame-sctc-frames iv (rest ∷ᶠ frame)))

  blame-sctc-pending-progress : ∀ {τ τᵣ eᵣ ℓ e} i →
    (⊨eown : ℐowner (suc i) ⊨[ ℓ ] e) →
    (ec : Ann ∣ e ⦂ τ ▷ eᵣ ⦂ τᵣ) →
    (tag : RuleTag) →
    (pending : PendingStep (AnnRules Ann tag) eᵣ) →
    (∃[ e′ ] 𝒯 (suc i) ⊢ Ok , e ⟶ Ok , e′) ⊎
    (∃[ eᵣ ] ∃[ bsκs ] ∃[ eκ ] Frame i e eᵣ bsκs eκ)
  blame-sctc-pending-progress i ⊨eown ec `R-cross-unit pending@record { tyVarsWit = refl }
    = inj₁ (_ ,
            R-bdr `R-cross-unit Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending (λ ()) (tt , tt , refl ,′ refl)))))
  blame-sctc-pending-progress i ⊨eown ec `R-cross-nat pending@(mkPendingStep refl termEnv (mkTerm ψ₁ refl) iv)
    with ec | proj₂(ψ₁(here refl)) in split-eq
  ... | ec | []
    = inj₁ (_ ,
            R-bdr `R-cross-nat Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ ())
                                              (tt , tt , Ok , (refl ,′ refl) ,′ subst-check-nat-sctcs)))))
    where
      check-nat-sctcs-ty : List (Blame × SCtc1N [] `ℕ) → Set
      check-nat-sctcs-ty bsκs =
        checkNatSCtcs 𝒜sctc-view (𝒯 i) (map proj₂ bsκs) (termEnv (here refl)) Ok Ok

      subst-check-nat-sctcs = subst check-nat-sctcs-ty (sym split-eq) refl
  ... | ec | ((b , flat l ep) ∷ bsκs)
    = inj₂ (_ , _ , _ , mkFrame pending
                                [ (b ,′ flat l ep) ]
                                ec
                                -- can be inferred; wrote down for clarity
                                {ℓₙ = proj₁ ℓₙ,ℓₚ} {ℓₚ = proj₂ ℓₙ,ℓₚ}
                                (subst  (ℐowner (suc i) ⊨[_] _)
                                        match-eq
                                        (proj₂ ℓₙ,⊨eᵣown))
                                refl
                                iv
                                split-eq
                                [ R-refl , refl ]ᶜ)
    where ℓₙ,ℓₚ = proj₁(ψ₁(here refl))

          ℓₙ,⊨eᵣown = idecompose-by-ectxt ec ⊨eown

          match-eq : proj₁ ℓₙ,⊨eᵣown ≡ proj₁ ℓₙ,ℓₚ
          match-eq with ℓₙ,⊨eᵣown
          ... | ℓₙ₁ , B/i .ℓₙ₁ ℓₚ ℓₙ₁◁ℓₚ
                          (bs-own-eq , j-κsat)
                          esat
            = cong proj₁ bs-own-eq
  blame-sctc-pending-progress i ⊨eown ec `R-cross-cons
    pending@record  { tyVarsWit = ((τ₁ , τ₂) , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-cross-cons Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where
                                                (here refl) →
                                                  Product.map₂ (map (Product.map₂ */c-sκ₁)) ⟨ℓₙ,ℓₚ⟩,bsκs
                                                (there (here refl)) →
                                                  Product.map₂ (map (Product.map₂ */c-sκ₂)) ⟨ℓₙ,ℓₚ⟩,bsκs)
                                              ( ( sym (List.map-∘ bsκs) ,′
                                                  sym (List.map-∘ bsκs) ) ,′
                                                (refl ,′ refl) ,′
                                                (refl ,′ refl) ,′
                                                (begin
                                                    map proj₂ (map (Product.map₂ */c-sκ₁) bsκs)
                                                  ≡⟨ List.map-∘ bsκs ⟨
                                                    map (*/c-sκ₁ ∘ proj₂) bsκs
                                                  ≡⟨ List.map-∘ bsκs ⟩
                                                    map */c-sκ₁ (map proj₂ bsκs)
                                                  ∎) ,′
                                                (begin
                                                    map proj₂ (map (Product.map₂ */c-sκ₂) bsκs)
                                                  ≡⟨ List.map-∘ bsκs ⟨
                                                    map (*/c-sκ₂ ∘ proj₂) bsκs
                                                  ≡⟨ List.map-∘ bsκs ⟩
                                                    map */c-sκ₂ (map proj₂ bsκs)
                                                  ∎))))))
    where ⟨ℓₙ,ℓₚ⟩,bsκs = ψ₁(here refl)
          bsκs = proj₂ ⟨ℓₙ,ℓₚ⟩,bsκs
  blame-sctc-pending-progress i ⊨eown ec `R-cross-inl
    pending@record  { tyVarsWit = ((τ₁ , τ₂) , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-cross-inl Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where
                                                (here refl) →
                                                  Product.map₂ (map (Product.map₂ +/c-sκ₁)) ⟨ℓₙ,ℓₚ⟩,bsκs)
                                              ( sym (List.map-∘ bsκs) ,′
                                                refl ,′
                                                (refl ,′ refl) ,′
                                                (begin
                                                    map proj₂ (map (Product.map₂ +/c-sκ₁) bsκs)
                                                  ≡⟨ List.map-∘ bsκs ⟨
                                                    map (+/c-sκ₁ ∘ proj₂) bsκs
                                                  ≡⟨ List.map-∘ bsκs ⟩
                                                    map +/c-sκ₁ (map proj₂ bsκs)
                                                  ∎))))))
    where ⟨ℓₙ,ℓₚ⟩,bsκs = ψ₁(here refl)
          bsκs = proj₂ ⟨ℓₙ,ℓₚ⟩,bsκs
  blame-sctc-pending-progress i ⊨eown ec `R-cross-inr
    pending@record  { tyVarsWit = ((τ₁ , τ₂) , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-cross-inr Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where
                                                (here refl) →
                                                  Product.map₂ (map (Product.map₂ +/c-sκ₂)) ⟨ℓₙ,ℓₚ⟩,bsκs)
                                              ( sym (List.map-∘ bsκs) ,′
                                                refl ,′
                                                (refl ,′ refl) ,′
                                                (begin
                                                    map proj₂ (map (Product.map₂ +/c-sκ₂) bsκs)
                                                  ≡⟨ List.map-∘ bsκs ⟨
                                                    map (+/c-sκ₂ ∘ proj₂) bsκs
                                                  ≡⟨ List.map-∘ bsκs ⟩
                                                    map +/c-sκ₂ (map proj₂ bsκs)
                                                  ∎))))))
    where ⟨ℓₙ,ℓₚ⟩,bsκs = ψ₁(here refl)
          bsκs = proj₂ ⟨ℓₙ,ℓₚ⟩,bsκs
  blame-sctc-pending-progress i ⊨eown ec `R-cross-roll
    pending@record  { tyVarsWit = (τ′ , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-cross-roll Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where
                                                (here refl) →
                                                  Product.map₂ (map (Product.map₂ μ/c-sκ)) ⟨ℓₙ,ℓₚ⟩,bsκs)
                                              ( sym (List.map-∘ bsκs) ,′
                                                refl ,′
                                                (refl ,′ refl) ,′
                                                (begin
                                                  map proj₂ (map (Product.map₂ μ/c-sκ) bsκs)
                                                ≡⟨ List.map-∘ bsκs ⟨
                                                  map (μ/c-sκ ∘ proj₂) bsκs
                                                ≡⟨ List.map-∘ bsκs ⟩
                                                  map μ/c-sκ (map proj₂ bsκs) ∎))))))
    where ⟨ℓₙ,ℓₚ⟩,bsκs = ψ₁(here refl)
          bsκs = proj₂ ⟨ℓₙ,ℓₚ⟩,bsκs
  blame-sctc-pending-progress i ⊨eown ec `R-cross-box
    pending@record  { tyVarsWit = (τ′ , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-cross-box Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending ψ₁ (refl ,′ refl ,′ (refl ,′ refl) ,′ refl)))))
  blame-sctc-pending-progress i ⊨eown ec `R-cross-lam
    pending@record  { tyVarsWit = ((τₐ , τᵣ) , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-cross-lam Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending ψ₁ (refl ,′ refl ,′ (refl ,′ refl) ,′ refl)))))
  blame-sctc-pending-progress i ⊨eown ec `R-merge-box
    pending@record  { tyVarsWit = (τ′ , refl)
                    ; termEnv = termEnv
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-merge-box Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where
                                                (here refl) → (proj₁ ℓₙ,ℓₚ ,′ proj₂ ℓ′ₙ,ℓ′ₚ) ,′
                                                              bsκs′ ++ bsκs)
                                              ( List.map-++ proj₁ bsκs′ bsκs ,′
                                                (refl ,′ match-eq) ,′
                                                (refl ,′ refl) ,′
                                                List.map-++ proj₂ bsκs′ bsκs)))))
    where ℓₙ,ℓₚ = proj₁(ψ₁(here refl))
          bsκs = proj₂(ψ₁(here refl))

          ℓ′ₙ,ℓ′ₚ = proj₁(ψ₁(there (here refl)))
          bsκs′ = proj₂(ψ₁(there (here refl)))

          ℓₙ,⊨eᵣown = idecompose-by-ectxt ec ⊨eown

          match-eq : proj₂ ℓₙ,ℓₚ ≡ proj₁ ℓ′ₙ,ℓ′ₚ
          match-eq with ℓₙ,⊨eᵣown
          ... | ℓₙ₁ , B/i .ℓₙ₁ ℓₚ ℓₙ₁◁ℓₚ
                          (bs-own-eq , j-κsat)
                          (proxy/i  .(box/m (termEnv(here refl)))
                                    ℓ′ₙ ℓ′ₚ ℓ′ₙ◁ℓ′ₚ
                                    (bs-own-eq′ , j-κsat′)
                                    esat)
            = trans (sym (cong proj₂ bs-own-eq)) (cong proj₁ bs-own-eq′)
  blame-sctc-pending-progress i ⊨eown ec `R-merge-lam
    pending@record  { tyVarsWit = ((τₐ , τᵣ) , refl)
                    ; termEnv = termEnv
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-merge-lam Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where
                                                (here refl) → (proj₁ ℓₙ,ℓₚ ,′ proj₂ ℓ′ₙ,ℓ′ₚ) ,′
                                                              bsκs′ ++ bsκs)
                                              ( List.map-++ proj₁ bsκs′ bsκs ,′
                                                (refl ,′ match-eq) ,′
                                                (refl ,′ refl) ,′
                                                List.map-++ proj₂ bsκs′ bsκs)))))
    where ℓₙ,ℓₚ = proj₁(ψ₁(here refl))
          bsκs = proj₂(ψ₁(here refl))

          ℓ′ₙ,ℓ′ₚ = proj₁(ψ₁(there (here refl)))
          bsκs′ = proj₂(ψ₁(there (here refl)))

          ℓₙ,⊨eᵣown = idecompose-by-ectxt ec ⊨eown

          match-eq : proj₂ ℓₙ,ℓₚ ≡ proj₁ ℓ′ₙ,ℓ′ₚ
          match-eq with ℓₙ,⊨eᵣown
          ... | ℓₙ₁ , B/i .ℓₙ₁ ℓₚ ℓₙ₁◁ℓₚ
                          (bs-own-eq , j-κsat)
                          (proxy/i  .(ƛ/m (termEnv(here refl)))
                                    ℓ′ₙ ℓ′ₚ ℓ′ₙ◁ℓ′ₚ
                                    (bs-own-eq′ , j-κsat′)
                                    esat)
            = trans (sym (cong proj₂ bs-own-eq)) (cong proj₁ bs-own-eq′)
  blame-sctc-pending-progress i ⊨eown ec `R-proxy-unbox
    pending@record { term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-proxy-unbox Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where
                                                (here refl) →
                                                  Product.map₂ (map (Product.map₂ box/c-sκ)) ⟨ℓₙ,ℓₚ⟩,bsκs)
                                              ( sym (List.map-∘ bsκs) ,′
                                                refl ,′
                                                (refl ,′ refl) ,′
                                                (begin
                                                  map proj₂ (map (Product.map₂ box/c-sκ) bsκs)
                                                ≡⟨ List.map-∘ bsκs ⟨
                                                  map (box/c-sκ ∘ proj₂) bsκs
                                                ≡⟨ List.map-∘ bsκs ⟩
                                                  map box/c-sκ (map proj₂ bsκs) ∎))))))
    where ⟨ℓₙ,ℓₚ⟩,bsκs = ψ₁(here refl)
          bsκs = proj₂ ⟨ℓₙ,ℓₚ⟩,bsκs
  blame-sctc-pending-progress i ⊨eown ec `R-proxy-β
    pending@record  { tyVarsWit = τₐ
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-proxy-β Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where
                                                (here refl) →
                                                  Product.map (λ ℓₙ,ℓₚ → proj₂ ℓₙ,ℓₚ ,′ proj₁ ℓₙ,ℓₚ)
                                                              (reverse ∘ map (Product.map blame-swap →/c-dom-sκ))
                                                              ⟨ℓₙ,ℓₚ⟩,bsκs
                                                (there (here refl)) →
                                                  Product.map₂ (map (Product.map₂ →/c-rng-sκ)) ⟨ℓₙ,ℓₚ⟩,bsκs)
                                              ( ((begin
                                                    map proj₁ (reverse (map (Product.map blame-swap →/c-dom-sκ) bsκs))
                                                  ≡⟨ List.reverse-map proj₁ (map (Product.map blame-swap →/c-dom-sκ) bsκs) ⟩
                                                    reverse (map proj₁ (map (Product.map blame-swap →/c-dom-sκ) bsκs))
                                                  ≡⟨ cong reverse (List.map-∘ bsκs) ⟨
                                                    reverse (map (blame-swap ∘ proj₁) bsκs)
                                                  ≡⟨ cong reverse (List.map-∘ bsκs) ⟩
                                                    reverse (map blame-swap (map proj₁ bsκs)) ∎) ,′
                                                  sym (List.map-∘ bsκs)) ,′
                                                (refl ,′ refl) ,′
                                                (refl ,′ refl) ,′
                                                (begin
                                                  map proj₂ (reverse (map (Product.map blame-swap →/c-dom-sκ) bsκs))
                                                ≡⟨ List.reverse-map proj₂ (map (Product.map blame-swap →/c-dom-sκ) bsκs) ⟩
                                                  reverse (map proj₂ (map (Product.map blame-swap →/c-dom-sκ) bsκs))
                                                ≡⟨ cong reverse (List.map-∘ bsκs) ⟨
                                                  reverse (map (→/c-dom-sκ ∘ proj₂) bsκs)
                                                ≡⟨ cong reverse (List.map-∘ bsκs) ⟩
                                                  reverse (map →/c-dom-sκ (map proj₂ bsκs)) ∎) ,′
                                                (begin
                                                  map proj₂ (map (Product.map₂ →/c-rng-sκ) bsκs)
                                                ≡⟨ List.map-∘ bsκs ⟨
                                                  map (→/c-rng-sκ ∘ proj₂) bsκs
                                                ≡⟨ List.map-∘ bsκs ⟩
                                                  map →/c-rng-sκ (map proj₂ bsκs) ∎))))))
    where ⟨ℓₙ,ℓₚ⟩,bsκs = ψ₁(here refl)
          bsκs = proj₂ ⟨ℓₙ,ℓₚ⟩,bsκs
