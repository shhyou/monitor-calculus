{-# OPTIONS --without-K --safe #-}

module Contract.Progress (Label : Set) where

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; trans; sym; subst; cong)

open import Data.Unit.Base as Unit using (⊤; tt) -- needed for the number typeclass
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base as List using (List; []; _∷_; [_]; lookup; _++_; reverse; map)
import Data.List.Properties as List
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)

import Data.Nat.Literals
open import Agda.Builtin.FromNat

private
  instance
    NumNumber : Number ℕ
    NumNumber = Data.Nat.Literals.number

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import OpSemantics.TypeSafety
open import Annotation.Language

𝒜sctc : AnnTerm
open import Contract.Common Label
open import Contract.Base Label 𝒜sctc as StdCtc hiding (𝒜sctc)

open AnnTerm 𝒜sctc
open AnnRule 𝒜sctc

AnnTerm.Ann   𝒜sctc τ = List (SCtc1N [] τ)
AnnTerm.State 𝒜sctc   = Status

𝒯 : ℕ → AnnTransit 𝒜sctc
𝒯 zero    = ∅tr
𝒯 (suc i) = 𝒯sctc id𝒜view (𝒯 i)

infix 6 ∎_
infixl 5 _►_checking⟨_∣_⟩
infixl 5 _∷ᶠ_

data Frames : Set where
  ∎_ : ∀ {τ} → (e : Ann ∣ [] ⊢ τ) → Frames
  _►_checking⟨_∣_⟩ :
    Frames →
    (eᵣ : Ann ∣ [] ⊢ `ℕ) →
    (eκ : Ann ∣ [] ⊢ `ℕ) →
    (sκs : List (SCtc1N [] `ℕ)) →
    Frames

record Frame (j : ℕ) {τ} e eᵣ sκs eκ : Set where
  constructor mkFrame
  no-eta-equality; pattern
  field
    pending : PendingStep (R-cross-nat Ann) eᵣ
    sκs-init : List (SCtc1N [] `ℕ)
    redex : Ann ∣ e ⦂ τ ▷ eᵣ ⦂ `ℕ
    {sκs-all} : List (SCtc1N [] `ℕ)
    {n} : Ann ∣ [] ⊢ `ℕ
    redex-eq : eᵣ ≡ B# sκs-all ⟪ n ⟫
    nval : Ann ∣ n isvalof `ℕ
    split-eq : sκs-all ≡ sκs-init ++ sκs
    chk-steps : CheckingSteps id𝒜view (𝒯 j) nval Ok Ok eκ sκs-init

accept-checking-frame : ∀ {j τ} {e : Ann ∣ [] ⊢ τ} {m eᵣ} →
  Ann ∣ m isvalof `ℕ →
  (frame : Frame j e eᵣ [] (`s m)) →
  ∃[ e′ ] 𝒯 (suc j) ⊢ Ok , e ⟶ Ok , e′
accept-checking-frame {j = j}
  iv
  (mkFrame  pending@(mkPendingStep refl termEnv (mkTerm ψ₁ refl) iv₁)
            sκs-init ec refl nval split-eq chk-steps)
  = _ ,
    R-bdr `R-cross-nat Ok Ok
            (proj₂ (plug-∃ ec (Pending⇒Step pending
                                            (λ ())
                                            (_ , (refl ,′ refl) ,′ subst-check-nat-sctcs))))

  where
    acc-checkNatSCtcs = proj₂ (accept-check-nat-sctcs id𝒜view (𝒯 j) refl chk-steps iv)

    check-nat-sctcs-ty : List (SCtc1N [] `ℕ) → Set
    check-nat-sctcs-ty sκs =
      checkNatSCtcs id𝒜view (𝒯 j) sκs (termEnv(here refl)) Ok Ok

    sκs-eq : sκs-init ≡ ψ₁(here refl)
    sκs-eq = sym (trans split-eq (List.++-identityʳ sκs-init))

    subst-check-nat-sctcs = subst check-nat-sctcs-ty sκs-eq acc-checkNatSCtcs

reject-checking-frame : ∀ {j τ} {e : Ann ∣ [] ⊢ τ} {sκs eᵣ} →
  (frame : Frame j e eᵣ sκs `z) →
  ∃[ l ] ∃[ e′ ] 𝒯 (suc j) ⊢ Ok , e ⟶ Err l , e′
reject-checking-frame {j = j} {sκs = sκs}
  (mkFrame  pending@(mkPendingStep refl termEnv (mkTerm ψ₁ refl) iv₁)
            sκs-init ec refl nval split-eq chk-steps)
  = _ , _ ,
    R-bdr `R-cross-nat Ok (Err (proj₁ l,checkNatSCtcs))
            (proj₂ (plug-∃ ec (Pending⇒Step pending
                                            (λ ())
                                            (_ , (refl ,′ refl) ,′ subst-check-nat-sctcs))))

  where
    l,checkNatSCtcs = reject-check-nat-sctcs id𝒜view (𝒯 j) sκs refl chk-steps

    check-nat-sctcs-ty : List (SCtc1N [] `ℕ) → Set
    check-nat-sctcs-ty sκs =
      checkNatSCtcs id𝒜view (𝒯 j) sκs (termEnv(here refl)) Ok (Err (proj₁ l,checkNatSCtcs))

    subst-check-nat-sctcs = subst check-nat-sctcs-ty (sym split-eq) (proj₂ l,checkNatSCtcs)

error-checking-frame : ∀ {j τ} {e : Ann ∣ [] ⊢ τ} {eᵣ eκ eκ′ sκs l} →
  𝒯 j ⊢ Ok , eκ ⟶ Err l , eκ′ →
  (frame : Frame j e eᵣ sκs eκ) →
  ∃[ e′ ] 𝒯 (suc j) ⊢ Ok , e ⟶ Err l , e′
error-checking-frame {j = j} {sκs = sκs} {l = l}
  err-step
  (mkFrame  pending@(mkPendingStep refl termEnv (mkTerm ψ₁ refl) iv₁)
            sκs-init ec refl nval split-eq chk-steps)
  = _ ,
    R-bdr `R-cross-nat Ok (Err l)
            (proj₂ (plug-∃ ec (Pending⇒Step pending
                                            (λ ())
                                            (_ , (refl ,′ refl) ,′ subst-check-nat-sctcs))))
  where
    err-checkNatSCtcs = error-check-nat-sctcs id𝒜view (𝒯 j) sκs refl chk-steps err-step refl

    check-nat-sctcs-ty : List (SCtc1N [] `ℕ) → Set
    check-nat-sctcs-ty sκs =
      checkNatSCtcs id𝒜view (𝒯 j) sκs (termEnv(here refl)) Ok (Err l)

    subst-check-nat-sctcs = subst check-nat-sctcs-ty (sym split-eq) err-checkNatSCtcs

mutual
  data SCtcFrames : ℕ → ℕ → Frames → Set where
    [_,_]ᶠ : ∀ {i j τ} →
      (j-eq : i ≡ j) →
      (e : Ann ∣ [] ⊢ τ) →
      SCtcFrames i j (∎ e)
    _∷ᶠ_ : ∀ {τ i j evs eᵣ eκ₁ eκ sκs} →
      (rest : SCtcFramesRest {τ} i (suc j) evs eκ₁) →
      (frame : Frame j eκ₁ eᵣ sκs eκ) →
      SCtcFrames i j (evs ► eᵣ checking⟨ eκ ∣ sκs ⟩)

  data SCtcFramesRest : ∀ {τ} → ℕ → ℕ → Frames → Ann ∣ [] ⊢ τ → Set where
    one : ∀ {τ i j} {e : Ann ∣ [] ⊢ τ} →
      (frames : SCtcFrames i j (∎ e)) →
      SCtcFramesRest i j (∎ e) e

    more : ∀ {i j evs eᵣ eκ sκs} →
      (frames : SCtcFrames i j (evs ► eᵣ checking⟨ eκ ∣ sκs ⟩)) →
      SCtcFramesRest i j (evs ► eᵣ checking⟨ eκ ∣ sκs ⟩) eκ

step-sctc-frames : ∀ {i j evs eᵣ eκ eκ′ sκs} →
  (step : 𝒯 j ⊢ Ok , eκ ⟶ Ok , eκ′) →
  SCtcFrames i j (evs ► eᵣ checking⟨ eκ  ∣ sκs ⟩) →
  SCtcFrames i j (evs ► eᵣ checking⟨ eκ′ ∣ sκs ⟩)
step-sctc-frames {j = j} step (frames ∷ᶠ mkFrame pending sκs-init ec redex-eq nval split-eq chk-steps) =
  frames ∷ᶠ mkFrame pending sκs-init ec redex-eq nval split-eq stepped-chk-steps
  where stepped-chk-steps = step-check-nat-sctcs id𝒜view (𝒯 j) step refl chk-steps

next-sctc-frames : ∀ {i j evs eᵣ m sκ sκs} →
  Ann ∣ m isvalof `ℕ →
  SCtcFrames i j (evs ► eᵣ checking⟨ `s m ∣ sκ ∷ sκs ⟩) →
  ∃[ eκ ] SCtcFrames i j (evs ► eᵣ checking⟨ eκ ∣ sκs ⟩)
next-sctc-frames {j = j} {sκ = sκ} {sκs} iv
  (frames ∷ᶠ mkFrame pending sκs-init ec redex-eq nval split-eq chk-steps)
  rewrite sym (List.++-assoc sκs-init [ sκ ] sκs)
  = _ , frames ∷ᶠ mkFrame pending (sκs-init ++ [ sκ ]) ec redex-eq nval split-eq (proj₂ eκ,chk-steps′)
  where eκ,chk-steps′ = next-checking-steps id𝒜view (𝒯 j) iv chk-steps sκ

mutual
  data SCtcProgress : ℕ → Frames → Set where
    SP-val : ∀ {i τ v} →
      (iv : Ann ∣ v isvalof τ) →
      SCtcProgress (suc i) (∎ v)

    SP-err : ∀ {i τ e} →
      (ec : Ann ∣ e ⦂ τ ▷ (assert `z) ⦂ `1) →
      SCtcProgress (suc i) (∎ e)

    SP-step : ∀ {i τ s′} {e e′ : Ann ∣ [] ⊢ τ} →
      𝒯 (suc i) ⊢ Ok , e ⟶ s′ , e′ →
      SCtcProgress (suc i) (∎ e)

    SP-start-checking : ∀ {τ i} {e : Ann ∣ [] ⊢ τ} {e₁ sκs eκ} →
      SCtcFrames   (suc i) i (∎ e ► e₁ checking⟨ eκ ∣ sκs ⟩) →
      SCtcProgress (suc i)   (∎ e)

  data SCtcBlames (l : Label) : ℕ → ℕ → Frames → Set where
    SB-blame : ∀ {τ i j} {e e′ : Ann ∣ [] ⊢ τ} →
      suc i ≡ j →
      𝒯 (suc i) ⊢ Ok , e ⟶ Err l , e′ →
      SCtcBlames l (suc i) j (∎ e)

    SB-frame : ∀ {i j evs e eκ eκ′ sκs} →
      SCtcBlames l (suc i) (suc j) evs →
      𝒯 j ⊢ Ok , eκ ⟶ Err l , eκ′ →
      SCtcBlames l (suc i) j (evs ► e checking⟨ eκ ∣ sκs ⟩)

  data SCtcCheckingProgress : ℕ → ℕ → Frames → Set where
    SCP-blame : ∀ {i j l evs e eκ sκs} →
      SCtcBlames         l (suc i) (suc j) evs →
      SCtcCheckingProgress (suc i) j       (evs ► e checking⟨ eκ ∣ sκs ⟩)

    SCP-finish-all-checking : ∀ {τ i} {e e′ : Ann ∣ [] ⊢ τ} {e₁ m} →
      (iv : Ann ∣ m isvalof `ℕ) →
      𝒯 (suc i) ⊢ Ok , e ⟶ Ok , e′ →
      SCtcCheckingProgress (suc i) i (∎ e ► e₁ checking⟨ `s m ∣ [] ⟩)

    SCP-finish-one-checking : ∀ {i j evs e₁ e₂ eκ eκ′ m sκs} →
      (iv : Ann ∣ m isvalof `ℕ) →
      𝒯 (suc j) ⊢ Ok , eκ ⟶ Ok , eκ′ →
      SCtcFrames           (suc i) (suc j) (evs ► e₁ checking⟨ eκ′ ∣ sκs ⟩) →
      SCtcCheckingProgress (suc i) j       (evs ► e₁ checking⟨ eκ  ∣ sκs ⟩ ► e₂ checking⟨ `s m ∣ [] ⟩)

    SCP-finish-one-sctc : ∀ {i j evs e eκ m sκ sκs} →
      (iv : Ann ∣ m isvalof `ℕ) →
      SCtcFrames           (suc i) j (evs ► e checking⟨ eκ   ∣ sκs ⟩) →
      SCtcCheckingProgress (suc i) j (evs ► e checking⟨ `s m ∣ sκ ∷ sκs ⟩)

    SCP-step : ∀ {i j evs e eκ eκ′ sκs} →
      𝒯 j ⊢ Ok , eκ ⟶ Ok , eκ′ →
      SCtcFrames           (suc i) j (evs ► e checking⟨ eκ′ ∣ sκs ⟩) →
      SCtcCheckingProgress (suc i) j (evs ► e checking⟨ eκ  ∣ sκs ⟩)

    SCP-err : ∀ {i j evs e eκ sκs} →
      (ec : Ann ∣ eκ ⦂ `ℕ ▷ (assert `z) ⦂ `1) →
      SCtcCheckingProgress (suc i) j (evs ► e checking⟨ eκ ∣ sκs ⟩)

    SCP-start-new-checking : ∀ {i j evs e₁ e₂ eκ eκ₂ sκs sκs′} →
      SCtcFrames           (suc i) j       (evs ► e₁ checking⟨ eκ ∣ sκs ⟩ ► e₂ checking⟨ eκ₂ ∣ sκs′ ⟩) →
      SCtcCheckingProgress (suc i) (suc j) (evs ► e₁ checking⟨ eκ ∣ sκs ⟩)

    SCP-pending : ∀ {i τ evs e₁ e₂ eκ sκs} →
      (ec : Ann ∣ eκ ⦂ `ℕ ▷ e₂ ⦂ τ) →
      (tag : RuleTag) →
      (pending : PendingStep (AnnRules Ann tag) e₂) →
      SCtcCheckingProgress (suc i) 0 (evs ► e₁ checking⟨ eκ ∣ sκs ⟩)

  sctc-progress : ∀ {τ} i (e : Ann ∣ [] ⊢ τ) → SCtcProgress (suc i) (∎ e)
  sctc-progress i e with progress Ok e
  ... | P-step step = SP-step (R-redex step)
  ... | P-err ec = SP-err ec
  ... | P-val iv = SP-val iv
  ... | P-pending ec tag pending with sctc-pending-progress i e ec tag pending
  ... | inj₁ (_ , step) = SP-step step
  ... | inj₂ (_ , _ , _ , frame) = SP-start-checking (one [ refl , e ]ᶠ ∷ᶠ frame)

  sctc-blames : ∀ {i j l evs e eκ eκ′ sκs} →
    𝒯 j ⊢ Ok , eκ ⟶ Err l , eκ′ →
    SCtcFrames   (suc i) j (evs ► e checking⟨ eκ ∣ sκs ⟩) →
    SCtcBlames l (suc i) j (evs ► e checking⟨ eκ ∣ sκs ⟩)
  sctc-blames step (one [ refl , e ]ᶠ ∷ᶠ frame) =
    SB-frame (SB-blame refl (proj₂ (error-checking-frame step frame))) step
  sctc-blames step (more frames ∷ᶠ frame) =
    SB-frame (sctc-blames (proj₂ (error-checking-frame step frame)) frames) step

  sctc-checking-progress : ∀ {i j eκ sκs evs e} →
    SCtcFrames           (suc i) j (evs ► e checking⟨ eκ ∣ sκs ⟩) →
    SCtcCheckingProgress (suc i) j (evs ► e checking⟨ eκ ∣ sκs ⟩)
  sctc-checking-progress {eκ = eκ} frames with progress Ok eκ
  sctc-checking-progress frames                   | P-step step =
    SCP-step (R-redex step) (step-sctc-frames (R-redex step) frames)
  sctc-checking-progress frames                   | P-err ec = SCP-err ec
  sctc-checking-progress {j = j} {eκ = eκ} frames | P-pending ec tag pending with j
  ... | zero     = SCP-pending ec tag pending
  ... | (suc j′) with sctc-pending-progress j′ eκ ec tag pending
  ... | inj₁ (_ , step) = SCP-step step (step-sctc-frames step frames)
  ... | inj₂ (_ , _ , _ , frame) = SCP-start-new-checking (more frames ∷ᶠ frame)
  sctc-checking-progress            (one [ refl , e ]ᶠ ∷ᶠ frame) | P-val z/v =
    SCP-blame (SB-blame refl (proj₂ (proj₂ (reject-checking-frame frame))))
  sctc-checking-progress            (more frames  ∷ᶠ frame)      | P-val z/v =
    SCP-blame (sctc-blames (proj₂ (proj₂ (reject-checking-frame frame))) frames)
  sctc-checking-progress {sκs = []} (one [ refl , e ]ᶠ ∷ᶠ frame) | P-val (s/v iv) =
    SCP-finish-all-checking iv (proj₂ (accept-checking-frame iv frame))
  sctc-checking-progress {sκs = []} (more frames ∷ᶠ frame)       | P-val (s/v iv) =
    SCP-finish-one-checking iv step (step-sctc-frames step frames)
    where step = proj₂ (accept-checking-frame iv frame)
  sctc-checking-progress {sκs = flat l ep ∷ sκs} (rest ∷ᶠ frame) | P-val (s/v iv) =
    SCP-finish-one-sctc iv (proj₂ (next-sctc-frames iv (rest ∷ᶠ frame)))

  sctc-pending-progress : ∀ {τ τᵣ eᵣ} i e →
    (ec : Ann ∣ e ⦂ τ ▷ eᵣ ⦂ τᵣ) →
    (tag : RuleTag) →
    (pending : PendingStep (AnnRules Ann tag) eᵣ) →
    (∃[ e′ ] 𝒯 (suc i) ⊢ Ok , e ⟶ Ok , e′) ⊎
    (∃[ eᵣ ] ∃[ sκs ] ∃[ eκ ] Frame i e eᵣ sκs eκ)
  sctc-pending-progress i e ec `R-cross-unit pending@record { tyVarsWit = refl }
    = inj₁ (_ ,
            R-bdr `R-cross-unit Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending (λ ()) (refl ,′ refl)))))
  sctc-pending-progress i e ec `R-cross-nat pending@(mkPendingStep refl termEnv (mkTerm ψ₁ refl) iv)
    with ec | ψ₁(here refl) in split-eq
  ... | ec | []
    = inj₁ (_ ,
            R-bdr `R-cross-nat Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ ())
                                              (Ok , (refl ,′ refl) ,′ subst-check-nat-sctcs)))))
    where
      check-nat-sctcs-ty : List (SCtc1N [] `ℕ) → Set
      check-nat-sctcs-ty sκs = checkNatSCtcs id𝒜view (𝒯 i) sκs (termEnv (here refl)) Ok Ok
      subst-check-nat-sctcs = subst check-nat-sctcs-ty (sym split-eq) refl
  ... | ec | (flat l ep ∷ sκs)
    = inj₂ (_ , _ , _ , mkFrame pending [ flat l ep ] ec refl iv split-eq [ R-refl , refl ]ᶜ)
  sctc-pending-progress i e ec `R-cross-cons
    pending@record  { tyVarsWit = ((τ₁ , τ₂) , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-cross-cons Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where
                                                (here refl) → map */c-sκ₁ (ψ₁ (here refl))
                                                (there (here refl)) → map */c-sκ₂ (ψ₁(here refl)))
                                              ((refl ,′ refl) ,′ refl ,′ refl)))))
  sctc-pending-progress i e ec `R-cross-inl
    pending@record  { tyVarsWit = ((τ₁ , τ₂) , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-cross-inl Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where (here refl) → map +/c-sκ₁ (ψ₁(here refl)))
                                              ((refl ,′ refl) ,′ refl)))))
  sctc-pending-progress i e ec `R-cross-inr
    pending@record  { tyVarsWit = ((τ₁ , τ₂) , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-cross-inr Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where (here refl) → map +/c-sκ₂ (ψ₁(here refl)))
                                              ((refl ,′ refl) ,′ refl)))))
  sctc-pending-progress i e ec `R-cross-roll
    pending@record  { tyVarsWit = (τ′ , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-cross-roll Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where (here refl) → map μ/c-sκ (ψ₁(here refl)))
                                              ((refl ,′ refl) ,′ refl)))))
  sctc-pending-progress i e ec `R-cross-box
    pending@record  { tyVarsWit = (τ′ , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-cross-box Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending ψ₁ ((refl ,′ refl) ,′ refl)))))
  sctc-pending-progress i e ec `R-cross-lam
    pending@record  { tyVarsWit = ((τₐ , τᵣ) , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-cross-lam Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending ψ₁ ((refl ,′ refl) ,′ refl)))))
  sctc-pending-progress i e ec `R-merge-box
    pending@record  { tyVarsWit = (τ′ , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-merge-box Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where
                                                (here refl) → ψ₁(there (here refl)) ++ ψ₁(here refl))
                                              ((refl ,′ refl) ,′ refl)))))
  sctc-pending-progress i e ec `R-merge-lam
    pending@record  { tyVarsWit = ((τₐ , τᵣ) , refl)
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-merge-lam Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where
                                                (here refl) → ψ₁(there (here refl)) ++ ψ₁(here refl))
                                              ((refl ,′ refl) ,′ refl)))))
  sctc-pending-progress i e ec `R-proxy-unbox
    pending@record { term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-proxy-unbox Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where (here refl) → map box/c-sκ (ψ₁(here refl)))
                                              ((refl ,′ refl) ,′ refl)))))
  sctc-pending-progress i e ec `R-proxy-β
    pending@record  { tyVarsWit = τₐ
                    ; term₁ = mkTerm ψ₁ refl }
    = inj₁ (_ ,
            R-bdr `R-proxy-β Ok Ok
              (proj₂ (plug-∃ ec (Pending⇒Step pending
                                              (λ where
                                                (here refl) → reverse (map →/c-dom-sκ (ψ₁(here refl)))
                                                (there (here refl)) → map →/c-rng-sκ (ψ₁(here refl)))
                                              ((refl ,′ refl) ,′ refl ,′ refl)))))
