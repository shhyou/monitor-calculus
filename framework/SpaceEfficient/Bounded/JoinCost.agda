{-# OPTIONS --safe --without-K #-}

open import Data.Nat.Base as Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s; _⊔_)
open import Data.List.Base as List using (List; []; _∷_; _++_; length; map)

open import Annotation.Language
open import SpaceEfficient.Bounded.Base
  using ()
  renaming (𝒜ccctc to SE𝒜ccctc; 𝒜cctc-view to SE𝒜cctc-view)
open import SpaceEfficient.OrderedPredicate
  using ()
  renaming (OrderedPredicate to SEOrderedPredicate)

module SpaceEfficient.Bounded.JoinCost
  (Label : Set)
  (OP : SEOrderedPredicate  Label (SE𝒜ccctc Label)
                            (AnnTermView.getState (SE𝒜cctc-view Label))
                            (AnnTermView.putState (SE𝒜cctc-view Label)))
  (H : ℕ)
  where

open import Relation.Nullary using (Dec; yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst; sym; trans; cong; module ≡-Reasoning)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Properties as Nat
  using (≤-refl; ≤-trans; module ≤-Reasoning)
open import Data.Product as Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

import Data.List.Properties as List
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Function.Base using (id; _∘′_; flip′)

open import Utils.Misc
open import Data.Tick using (Tick; evalTick; execTick; ✓_)
open import Data.RawFilter using (𝕌)
open import Data.IsNonEmpty
open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Interpretation
open import Annotation.Soundness

open SpaceEfficient.Bounded.Base Label
open import Contract.Common Label
open import Contract.Base Label 𝒜ccctc
open SpaceEfficient.OrderedPredicate Label 𝒜ccctc
open import SpaceEfficient.Base Label 𝒜ccctc
open import SpaceEfficient.Height Label 𝒜ccctc
open import SpaceEfficient.Size Label 𝒜ccctc
open import SpaceEfficient.NonRecursive Label 𝒜ccctc
open import SpaceEfficient.LeafPredicate Label 𝒜ccctc
open import SpaceEfficient.Cost.Checking Label 𝒜ccctc
open import SpaceEfficient.Cost.Join Label 𝒜ccctc
open import SpaceEfficient.Bounded.OpSemantics Label (OrderedPredicate.stronger? OP)
open import SpaceEfficient.Properties.UniqueSublist Label 𝒜cctc-view OP
open import SpaceEfficient.Properties.NonEmpty Label 𝒜cctc-view (OrderedPredicate.stronger? OP)
open import SpaceEfficient.Properties.Height Label 𝒜cctc-view (OrderedPredicate.stronger? OP)
open import SpaceEfficient.Properties.Size Label 𝒜cctc-view (OrderedPredicate.stronger? OP)
open import SpaceEfficient.Properties.NonRecursive Label 𝒜cctc-view (OrderedPredicate.stronger? OP)
open AnnTerm 𝒜ccctc hiding (State)

open OrderedPredicate OP renaming (isPartialOrder to opIsPartialOrder)
open SECtcTransitSteps 𝒜cctc-view stronger?

open import SpaceEfficient.TimeComplexity Label 𝒜cctc-view stronger?

open join-flats-quadratic drop-is-linear using (join-flats-is-quadratic)
open join-expquad join-flats-is-quadratic using (join-c₀; join-is-exp-quadratic)


join-bound : (c : ℕ) → (U : List Pred) → (h : ℕ) → ℕ
join-bound c U h = c * ((length U ^ 2) * 2 ^ h)

ℐsebnd : (c : ℕ) → AnnIntr 𝒯cntctc
AnnIntr.Ix         (ℐsebnd _) = ⊤
AnnIntr.IxRel      (ℐsebnd _) cκ ix ix′ = ⊤
AnnIntr.Ord        (ℐsebnd _) = trivialOrd
AnnIntr.isPreorder (ℐsebnd _) = trivialOrdIsPreorder
AnnIntr.Inv        (ℐsebnd c) s = State.cost/se s ≤ State.count s * join-bound c ord-preds H
AnnIntr.𝔹          (ℐsebnd _) cκ ix◁ix′ e =
  SECtcNonRecursive cκ ×
  SECtcPreds IsNonEmpty cκ ×
  SECtcPreds (ord-preds ⊇#_) cκ ×
  SECtcMaxH cκ H
AnnIntr.𝔹Sound     (ℐsebnd _) (R-redex step)            inv inv′ mono cnr,cne,c#⊆U,cmh = cnr,cne,c#⊆U,cmh
AnnIntr.𝔹Sound     (ℐsebnd _) (R-bdr rule-no s s′ step) inv inv′ mono cnr,cne,c#⊆U,cmh = cnr,cne,c#⊆U,cmh
AnnIntr.ℙ          (ℐsebnd c) cκ ix◁ix′ em =
  AnnIntr.𝔹 (ℐsebnd c) cκ ix◁ix′ ⌊ em ⌋m




se-c₀           : ℕ
join-c₀≤se-c₀   : 𝕌.base join-is-exp-quadratic ≤ se-c₀
1≤|ord-preds|   = IsNonEmpty-length ord-preds-nonempty

join-exp-quadratic : ∀ {Δ τ cκ cκ′} →
  SECtcPreds ((1 ≤_) ∘′ length) {Δ} {τ} cκ →
  SECtcPreds ((1 ≤_) ∘′ length) {Δ} {τ} cκ′ →
  execTick (✓ join cκ cκ′) ≤
    se-c₀ * (((leaf-size cκ ⊔ leaf-size cκ′ ⊔ 1) ^ 2) * (2 ^ (sectc-height cκ ⊔ sectc-height cκ′)))
join-exp-quadratic {cκ = cκ} {cκ′} cps-ne cps-ne′ =
  𝕌.ultimately (𝕌.ultimately join-is-exp-quadratic se-c₀ join-c₀≤se-c₀)
    (_ , _ , cκ ,′ cκ′)
    (cps-ne ,′ cps-ne′)

join-bounded : ∀ {Δ τ cκ cκ′} →
  SECtcPreds IsNonEmpty {Δ} {τ} cκ →
  SECtcPreds (ord-preds ⊇#_) cκ →
  SECtcMaxH cκ H →
  SECtcPreds IsNonEmpty {Δ} {τ} cκ′ →
  SECtcPreds (ord-preds ⊇#_) cκ′ →
  SECtcMaxH cκ′ H →
  execTick (✓ join cκ cκ′) ≤ se-c₀ * ((length ord-preds ^ 2) * (2 ^ H))
join-bounded {cκ = cκ} {cκ′} cne cκ-us cmh cne′ cκ-us′ cmh′ = begin
  execTick (✓ join cκ cκ′)
    ≤⟨ join-exp-quadratic (cps-map IsNonEmpty-length cne) (cps-map IsNonEmpty-length cne′) ⟩
  se-c₀ * (((leaf-size cκ ⊔ leaf-size cκ′ ⊔ 1) ^ 2) * (2 ^ (sectc-height cκ ⊔ sectc-height cκ′)))
    ≤⟨ Nat.*-monoʳ-≤ se-c₀ (Nat.*-monoˡ-≤ 2^heights (Nat.^-monoˡ-≤ 2 leaf-sizes≤U)) ⟩
  se-c₀ * ((length ord-preds ^ 2) * (2 ^ (sectc-height cκ ⊔ sectc-height cκ′)))
    ≤⟨ Nat.*-monoʳ-≤ se-c₀ (Nat.*-monoʳ-≤ U² (Nat.^-monoʳ-≤ 2 sectc-heights≤H)) ⟩
  se-c₀ * ((length ord-preds ^ 2) * (2 ^ H)) ∎
  where open ≤-Reasoning

        2^heights = 2 ^ (sectc-height cκ ⊔ sectc-height cκ′)
        U² = length ord-preds ^ 2

        leaf-sizes≤U : leaf-size cκ ⊔ leaf-size cκ′ ⊔ 1 ≤ length ord-preds
        leaf-sizes≤U = begin
          leaf-size cκ ⊔ leaf-size cκ′ ⊔ 1
            ≤⟨ Nat.⊔-monoˡ-≤ 1
                  (Nat.⊔-lub  (cps-leaf-size-bound (cps-map USublist-length cκ-us))
                              (cps-leaf-size-bound (cps-map USublist-length cκ-us′))) ⟩
          length ord-preds ⊔ 1
            ≤⟨ Nat.⊔-lub ≤-refl 1≤|ord-preds| ⟩
          length ord-preds ∎

        sectc-heights≤H : sectc-height cκ ⊔ sectc-height cκ′ ≤ H
        sectc-heights≤H = Nat.⊔-lub (cmh-height cmh) (cmh-height cmh′)



se-c₀ = 𝕌.base join-is-exp-quadratic
join-c₀≤se-c₀ = ≤-refl

ℐsebnd-monotonic : AnnTransitInterpIs (ℐsebnd se-c₀) Monotonic
ℐsebnd-monotonic `R-cross-unit {s₁ = s₁}
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , (s₁-status-eq , refl) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * join-bound se-c₀ ord-preds H) (join-bound se-c₀ ord-preds H)) ,
    tt
ℐsebnd-monotonic `R-cross-nat {s₁ = s₁} {s₂}
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (s₃ , (.s₁ , (s₁-status-eq , refl) , cκ-checks-tr) ,
                (s₄ , s₄-chkcost-eq@refl , (s₅ , s₅-secost-eq@refl , s₂-cnt-eq@refl))))
  esat
  (record { inv = I; boundarySat = _ , cnr , cne , cκ-us , cmh }) =
    (begin
      State.cost/se s₃                        ≡⟨ proj₁ (proj₂ s₃-chkcost,s₃-secost,cnt-eq) ⟨
      State.cost/se s₁                        ≤⟨ I ⟩
      State.count s₁ * se-cost                ≤⟨ Nat.m≤n+m (State.count s₁ * se-cost) se-cost ⟩
      se-cost + State.count s₁ * se-cost      ≡⟨ cong ((se-cost +_) ∘′ (_* se-cost))
                                                      (proj₂ (proj₂ s₃-chkcost,s₃-secost,cnt-eq)) ⟩
      se-cost + State.count s₃ * se-cost      ≡⟨⟩
      suc (State.count s₃) * se-cost          ∎) ,
    tt
    where
      open ≤-Reasoning

      se-cost = join-bound se-c₀ ord-preds H

      cκ-preds = flat/cc-preds (ψ₁(here refl))

      s₃-chkcost,s₃-secost,cnt-eq : State.cost/chk s₁ ≡ State.cost/chk s₃ ×
                                    State.cost/se s₁ ≡ State.cost/se s₃ ×
                                    State.count s₁ ≡ State.count s₃
      s₃-chkcost,s₃-secost,cnt-eq =
        check-nat-cctc-preserve-state cκ-preds
                                      (subst check-nat-ty (flat/cc-η (ψ₁(here refl))) cκ-checks-tr)
        where check-nat-ty = λ cκ → checkNatSECtc cκ (termEnv(here refl)) s₁ s₃
ℐsebnd-monotonic `R-cross-cons {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq₁ , cκ-eq₂) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * join-bound se-c₀ ord-preds H) (join-bound se-c₀ ord-preds H)) ,
    tt
ℐsebnd-monotonic `R-cross-inl {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * join-bound se-c₀ ord-preds H) (join-bound se-c₀ ord-preds H)) ,
    tt
ℐsebnd-monotonic `R-cross-inr {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * join-bound se-c₀ ord-preds H) (join-bound se-c₀ ord-preds H)) ,
    tt
ℐsebnd-monotonic `R-cross-roll {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * join-bound se-c₀ ord-preds H) (join-bound se-c₀ ord-preds H)) ,
    tt
ℐsebnd-monotonic `R-cross-box {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * join-bound se-c₀ ord-preds H) (join-bound se-c₀ ord-preds H)) ,
    tt
ℐsebnd-monotonic `R-cross-lam {s₁ = s₁}
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * join-bound se-c₀ ord-preds H) (join-bound se-c₀ ord-preds H)) ,
    tt
ℐsebnd-monotonic `R-merge-box {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (s₂ , refl , refl))))
  esat
  (record { boundarySat = (_ , cnr , cne , cκ-us , cmh) , (_ , cnr′ , cne′ , cκ-us′ , cmh′)
          ; inv = I }) =
    (begin
      State.cost/se s₁ + execTick (✓ join cκ′ cκ)
        ≤⟨ Nat.+-monoʳ-≤ (State.cost/se s₁) (join-bounded cne′ cκ-us′ cmh′ cne cκ-us cmh) ⟩
      State.cost/se s₁ + se-cost          ≤⟨ Nat.+-monoˡ-≤ se-cost I ⟩
      State.count s₁ * se-cost + se-cost  ≡⟨ Nat.+-comm (State.count s₁ * se-cost) se-cost ⟩
      se-cost + State.count s₁ * se-cost  ≡⟨⟩
      suc (State.count s₁) * se-cost      ∎) ,
    tt
    where
      open ≤-Reasoning
      cκ      = ψ₁(here refl)
      cκ′     = ψ₁(there (here refl))
      se-cost = join-bound se-c₀ ord-preds H
ℐsebnd-monotonic `R-merge-lam {s₁ = s₁}
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (s₂ , refl , refl))))
  esat
  (record { boundarySat = (_ , cnr , cne , cκ-us , cmh) , (_ , cnr′ , cne′ , cκ-us′ , cmh′)
          ; inv = I }) =
    (begin
      State.cost/se s₁ + execTick (✓ join cκ′ cκ)
        ≤⟨ Nat.+-monoʳ-≤ (State.cost/se s₁) (join-bounded cne′ cκ-us′ cmh′ cne cκ-us cmh) ⟩
      State.cost/se s₁ + se-cost          ≤⟨ Nat.+-monoˡ-≤ se-cost I ⟩
      State.count s₁ * se-cost + se-cost  ≡⟨ Nat.+-comm (State.count s₁ * se-cost) se-cost ⟩
      se-cost + State.count s₁ * se-cost  ≡⟨⟩
      suc (State.count s₁) * se-cost      ∎) ,
    tt
    where
      open ≤-Reasoning
      cκ      = ψ₁(here refl)
      cκ′     = ψ₁(there (here refl))
      se-cost = join-bound se-c₀ ord-preds H
ℐsebnd-monotonic `R-proxy-unbox {s₁ = s₁}
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * join-bound se-c₀ ord-preds H) (join-bound se-c₀ ord-preds H)) ,
    tt
ℐsebnd-monotonic `R-proxy-β {s₁ = s₁}
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκₐ-eq , cκᵣ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  Esat
  (record { inv = I }) =
    ≤-trans I (Nat.m≤n+m (State.count s₁ * join-bound se-c₀ ord-preds H) (join-bound se-c₀ ord-preds H)) ,
    tt


ℐsebnd-sound : AnnTransitInterpIs (ℐsebnd se-c₀) Sound
ℐsebnd-sound `R-cross-unit {s₁ = s₁}
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , (s₁-status-eq , refl) , (.s₁ , refl , (.s₁ , refl , refl))))
  esat termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = tt
    ; boundarySat = tt
    }
ℐsebnd-sound `R-cross-nat {s₁ = s₁} {s₂}
  (mkStep refl termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (s₃ , (.s₁ , (s₁-status-eq , refl) , cκ-checks-tr) ,
                (s₄ , s₄-chkcost-eq@refl , (s₅ , s₅-secost-eq@refl , s₂-cnt-eq@refl))))
  esat termSat inv′,mono = record
    { annCtxtIx = λ ()
    ; annIx = λ ()
    ; isTermIx = id
    ; boundarySat = tt
    }
ℐsebnd-sound `R-cross-cons {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq₁ , cκ-eq₂) , (.s₁ , refl , (.s₁ , refl , refl))))
  (B/i ix ix′ ix◁ix′ bsat (esat₁ `, esat₂))
  (record { boundarySat = _ , cnr , cne , cκ-us , cmh })
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix &&ix1↦ ix ]
    ; annIx = [ix0↦ ix′ &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
        ( tt ,
          subst SECtcNonRecursive (sym cκ-eq₁) (cnr-*₁ cnr) ,′
          subst (SECtcPreds IsNonEmpty) (sym cκ-eq₁) (cps-*₁ cne) ,′
          subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq₁) (cps-*₁ cκ-us) ,′
          subst (flip′ SECtcMaxH H) (sym cκ-eq₁) (cmh-*₁ cmh) ) ,′
        ( tt ,
          subst SECtcNonRecursive (sym cκ-eq₂) (cnr-*₂ cnr) ,′
          subst (SECtcPreds IsNonEmpty) (sym cκ-eq₂) (cps-*₂ cne) ,′
          subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq₂) (cps-*₂ cκ-us) ,′
          subst (flip′ SECtcMaxH H) (sym cκ-eq₂) (cmh-*₂ cmh) )
    }
ℐsebnd-sound `R-cross-inl {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  (B/i ix ix′ ix◁ix′ bsat (inl esat))
  (record { boundarySat = _ , cnr , cne , cκ-us , cmh })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-+₁ cnr) ,′
        subst (SECtcPreds IsNonEmpty) (sym cκ-eq) (cps-+₁ cne) ,′
        subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) (cps-+₁ cκ-us) ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-+₁ cmh)
    }
ℐsebnd-sound `R-cross-inr {s₁ = s₁}
  (mkStep ((τ₁ , τ₂) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  (B/i ix ix′ ix◁ix′ bsat (inr esat))
  (record { boundarySat = _ , cnr , cne , cκ-us , cmh })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-+₂ cnr) ,′
        subst (SECtcPreds IsNonEmpty) (sym cκ-eq) (cps-+₂ cne) ,′
        subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) (cps-+₂ cκ-us) ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-+₂ cmh)
    }
ℐsebnd-sound `R-cross-roll {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  (B/i ix ix′ ix◁ix′ bsat (roll .τ′ esat))
  (record { boundarySat = _ , cnr@() , cne , cκ-us , cmh }) -- cnr@() IMPOSSIBLE
  inv′,mono
ℐsebnd-sound `R-cross-box {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  (B/i ix ix′ ix◁ix′ bsat (box esat))
  (record { boundarySat = _ , cnr , cne , cκ-us , cmh })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) cnr ,′
        subst (SECtcPreds IsNonEmpty) (sym cκ-eq) cne ,′
        subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) cκ-us ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) cmh
    }
ℐsebnd-sound `R-cross-lam {s₁ = s₁}
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  (B/i ix ix′ ix◁ix′ bsat (ƛ esat))
  (record { boundarySat = _ , cnr , cne , cκ-us , cmh })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) cnr ,′
        subst (SECtcPreds IsNonEmpty) (sym cκ-eq) cne ,′
        subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) cκ-us ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) cmh
    }
ℐsebnd-sound `R-merge-box {s₁ = s₁}
  (mkStep (τ′ , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) ,
                  (s₂ , chkcost-eq@refl , (s₄ , s₄-secost-eq@refl , s₃-cnt-eq@refl))))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (box/m eₘ) .ix′ ix″ ix′◁ix″ psat (box esatm)))
  (record { inv = I ; boundarySat = (_ , cnr , cne , cκ-us , cmh) , (_ , cnr′ , cne′ , cκ-us′ , cmh′) })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-join cnr′ cnr) ,′
        subst (SECtcPreds IsNonEmpty) (sym cκ-eq)
              (cps-join 𝒜cctc-view stronger? nelist-join-flats cne′ cne) ,′ 
        subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq)
              (cps-join 𝒜cctc-view stronger? usublist-join-flats cκ-us′ cκ-us) ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-join cmh′ cmh)
    }
ℐsebnd-sound `R-merge-lam {s₁ = s₁}
  (mkStep ((τₐ , τᵣ) , refl) termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) ,
                  (s₂ , cost-eq@refl , (s₄ , s₄-secost-eq@refl , s₃-cnt-eq@refl))))
  (B/i ix ix′ ix◁ix′ bsat (proxy/i (ƛ/m eb) .ix′ ix″ ix′◁ix″ psat (ƛ esat)))
  (record { inv = I ; boundarySat = (_ , cnr , cne , cκ-us , cmh) , (_ , cnr′ , cne′ , cκ-us′ , cmh′) })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-join cnr′ cnr) ,′
        subst (SECtcPreds IsNonEmpty) (sym cκ-eq)
              (cps-join 𝒜cctc-view stronger? nelist-join-flats cne′ cne) ,′
        subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq)
              (cps-join 𝒜cctc-view stronger? usublist-join-flats cκ-us′ cκ-us) ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-join cmh′ cmh)
    }
ℐsebnd-sound `R-proxy-unbox {s₁ = s₁}
  (mkStep tt termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  (unbox (proxy/i em ix ix′ ix◁ix′ psat (box esat)))
  (record { boundarySat = _ , cnr , cne , cκ-us , cmh })
  inv′,mono = record
    { annCtxtIx = [ix↦ ix ]
    ; annIx = [ix↦ ix′ ]
    ; isTermIx = refl ,′ id
    ; boundarySat =
        tt ,
        subst SECtcNonRecursive (sym cκ-eq) (cnr-box cnr) ,′
        subst (SECtcPreds IsNonEmpty) (sym cκ-eq) (cps-box cne) ,′
        subst (SECtcPreds (ord-preds ⊇#_)) (sym cκ-eq) (cps-box cκ-us) ,′
        subst (flip′ SECtcMaxH H) (sym cκ-eq) (cmh-box cmh)
    }
ℐsebnd-sound `R-proxy-β {s₁ = s₁}
  (mkStep τₐ termEnv (mkTerm ψ₁ refl) (mkTerm ψ₂ refl) premWit
          (.s₁ , ((s₁-status-eq , refl) , cκₐ-eq , cκᵣ-eq) , (.s₁ , refl , (.s₁ , refl , refl))))
  ((proxy/i em ix ix′ ix◁ix′ psat (ƛ esat)) · esatₐ)
  (record { boundarySat = _ , cnr , cne , cκ-us , cmh })
  inv′,mono = record
    { annCtxtIx = [ix0↦ ix′ &&ix1↦ ix ]
    ; annIx = [ix0↦ ix &&ix1↦ ix′ ]
    ; isTermIx = refl ,′ id ,′ refl ,′ id
    ; boundarySat =
        ( tt ,
          subst SECtcNonRecursive (sym cκᵣ-eq) (cnr-rng cnr) ,′
          subst (SECtcPreds IsNonEmpty) (sym cκᵣ-eq) (cps-rng cne) ,′
          subst (SECtcPreds (ord-preds ⊇#_)) (sym cκᵣ-eq) (cps-rng cκ-us) ,′
          subst (flip′ SECtcMaxH H) (sym cκᵣ-eq) (cmh-rng cmh) ) ,′
        ( tt ,
          subst SECtcNonRecursive (sym cκₐ-eq) (cnr-dom cnr) ,′
          subst (SECtcPreds IsNonEmpty) (sym cκₐ-eq) (cps-dom cne) ,′
          subst (SECtcPreds (ord-preds ⊇#_)) (sym cκₐ-eq) (cps-dom cκ-us) ,′
          subst (flip′ SECtcMaxH H) (sym cκₐ-eq) (cmh-dom cmh) )
    }

join-cost-bounded : ∀ {τ s′} {e e′ : Ann ∣ [] ⊢ τ} →
  𝒯cntctc ⊢ init-state , e ⟶* s′ , e′ →
  ℐsebnd join-c₀ ⊨[ tt ] e →
  State.cost/se s′ ≤ State.count s′ * (se-c₀ * ((length ord-preds ^ 2) * (2 ^ H)))
join-cost-bounded steps ⊨e =
  proj₁ (monotonicity* (ℐsebnd join-c₀) ℐsebnd-monotonic ℐsebnd-sound steps z≤n ⊨e)
