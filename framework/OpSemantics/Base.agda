{-# OPTIONS --without-K --safe #-}

module OpSemantics.Base where

open import Utils.Misc
open import Syntax.Type
open import Syntax.Term
open import Annotation.Language

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; subst)

open import Data.Unit.Base as Unit using (⊤; tt) -- needed for the number typeclass
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃₂; ∃-syntax; _×_; _,′_)

open import Data.List.Base using (List; []; _∷_; lookup)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; any?; here; there)
open import Data.List.Membership.Propositional using (_∈_)

import Data.Nat.Literals
open import Agda.Builtin.FromNat

infix 5 _⟶r_
infix 5 _⊢_,_⟶_,_

private variable
  𝒜 : AnnTerm
  𝒯 : AnnTransit 𝒜
  Γ : Ctxt
  τ τ′ τₐ τᵣ τ₁ τ₂ : Ty

ReductionRel : ∀ 𝒜 → Set₁
ReductionRel 𝒜 = let open AnnTerm 𝒜 in
  ∀ {τ} → State → Ann ∣ [] ⊢ τ → State → Ann ∣ [] ⊢ τ → Set

data CtxtRel 𝒜 (R : ReductionRel 𝒜) : ReductionRel 𝒜
data _⟶r_ {Ann : AnnSig} : (e e′ : Ann ∣ [] ⊢ τ) → Set

BetaRel : ReductionRel 𝒜
BetaRel {𝒜} s e s′ e′ = (e ⟶r e′)

data _⊢_,_⟶_,_ (𝒯 : AnnTransit 𝒜) : ReductionRel 𝒜 where
  R-redex :
    ∀ {τ s} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    (step : CtxtRel 𝒜 BetaRel s e s e′) →
    𝒯 ⊢ s , e ⟶ s , e′

  R-bdr : let open AnnTerm 𝒜 in
    ∀ {τ} (tag : RuleTag) (s s′ : State) {e e′ : Ann ∣ [] ⊢ τ} →
      (step : CtxtRel 𝒜 (ATStep 𝒜 (AnnRules Ann tag , 𝒯 tag)) s e s′ e′) →
      𝒯 ⊢ s , e ⟶ s′ , e′

data _⟶r_ {Ann} where
    R-foldz : ∀ {τ es} {ez : Ann ∣ [] ⊢ τ} →
      foldN `z ez es ⟶r ez

    R-folds : ∀ {τ es v} {ez : Ann ∣ [] ⊢ τ} →
      (iv : Ann ∣ v isvalof `ℕ) →
      foldN (`s v) ez es ⟶r esubst es [x0↦ v &&x1↦ foldN v ez es ]

    R-assert : ∀ {v} →
      (iv : Ann ∣ v isvalof `ℕ) →
      assert (`s v) ⟶r ⋆

    R-outl : ∀ {v₁ v₂} →
      (iv₁ : Ann ∣ v₁ isvalof τ₁) →
      (iv₂ : Ann ∣ v₂ isvalof τ₂) →
      π₁ (v₁ `, v₂) ⟶r v₁

    R-outr : ∀ {v₁ v₂} →
      (iv₁ : Ann ∣ v₁ isvalof τ₁) →
      (iv₂ : Ann ∣ v₂ isvalof τ₂) →
      π₂ (v₁ `, v₂) ⟶r v₂

    R-casel : ∀ {v} →
      {e₁ : Ann ∣ (τ₁ ∷ []) ⊢ τ} →
      {e₂ : Ann ∣ (τ₂ ∷ []) ⊢ τ} →
      (iv : Ann ∣ v isvalof τ₁) →
      case (inl v) of e₁ ∣ e₂ ⟶r esubst e₁ [x0↦ v ]

    R-caser : ∀ {v} →
      {e₁ : Ann ∣ (τ₁ ∷ []) ⊢ τ} →
      {e₂ : Ann ∣ (τ₂ ∷ []) ⊢ τ} →
      (iv : Ann ∣ v isvalof τ₂) →
      case (inr v) of e₁ ∣ e₂ ⟶r esubst e₂ [x0↦ v ]

    R-unbox : ∀ {v} →
      (iv : Ann ∣ box v isvalof Box τ) →
      unbox (box v) ⟶r v

    R-β : ∀ {v} →
      {e : Ann ∣ (τₐ ∷ []) ⊢ τᵣ} →
      (iv : Ann ∣ v isvalof τₐ) →
      (ƛ e) · v ⟶r esubst e [x0↦ v ]

    R-unroll : ∀ {τ v} →
      (iv : Ann ∣ v isvalof (tsubst τ [t0↦ μ τ ])) →
      unroll (roll τ v) ⟶r v

    R-fix :
      {e : Ann ∣ (τ ∷ []) ⊢ τ} →
      fix e ⟶r esubst e [x0↦ fix e ]

    R-seq : ∀ {v} →
      {e : Ann ∣ [] ⊢ τ′} →
      (iv : Ann ∣ v isvalof τ) →
      v ⨟ e ⟶r e

data CtxtRel 𝒜 R where
    RC-here : ∀ {s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
      (step : R s e s′ e′) →
      CtxtRel 𝒜 R {τ} s e s′ e′

    RC-B : ∀ {A s s′ e e′} →
      CtxtRel 𝒜 R     s e            s′ e′ →
      CtxtRel 𝒜 R {τ} s (B# A ⟪ e ⟫) s′ (B# A ⟪ e′ ⟫)

    RC-s : ∀ {s s′ e e′} →
      CtxtRel 𝒜 R s e      s′ e′ →
      CtxtRel 𝒜 R s (`s e) s′ (`s e′)

    RC-foldN : ∀ {s s′ e e′ ez es} →
      CtxtRel 𝒜 R     s e               s′ e′ →
      CtxtRel 𝒜 R {τ} s (foldN e ez es) s′ (foldN e′ ez es)

    RC-assert : ∀ {s s′ e e′} →
      CtxtRel 𝒜 R s e          s′ e′ →
      CtxtRel 𝒜 R s (assert e) s′ (assert e′)

    RC-consl : ∀ {s s′ e₁ e₁′ e₂} →
      CtxtRel 𝒜 R {τ₁}       s e₁         s′ e₁′ →
      CtxtRel 𝒜 R {τ₁ `* τ₂} s (e₁ `, e₂) s′ (e₁′ `, e₂)

    RC-consr : ∀ {s s′ e e′ v} →
      (iv : ATAnn 𝒜 ∣ v isvalof τ₁) →
      CtxtRel 𝒜 R {τ₂}       s e        s′ e′ →
      CtxtRel 𝒜 R {τ₁ `* τ₂} s (v `, e) s′ (v `, e′)

    RC-outl : ∀ {s s′ e e′} →
      CtxtRel 𝒜 R {τ₁ `* τ₂} s e      s′ e′ →
      CtxtRel 𝒜 R {τ₁}       s (π₁ e) s′ (π₁ e′)

    RC-outr : ∀ {s s′ e e′} →
      CtxtRel 𝒜 R {τ₁ `* τ₂} s e      s′ e′ →
      CtxtRel 𝒜 R {τ₂}       s (π₂ e) s′ (π₂ e′)

    RC-inl : ∀ {s s′ e e′} →
      CtxtRel 𝒜 R {τ₁}       s e       s′ e′ →
      CtxtRel 𝒜 R {τ₁ `+ τ₂} s (inl e) s′ (inl e′)

    RC-inr : ∀ {s s′ e e′} →
      CtxtRel 𝒜 R {τ₂}       s e       s′ e′ →
      CtxtRel 𝒜 R {τ₁ `+ τ₂} s (inr e) s′ (inr e′)

    RC-case : ∀ {s s′ e e′ e₁ e₂} →
      CtxtRel 𝒜 R {τ₁ `+ τ₂} s e                   s′ e′ →
      CtxtRel 𝒜 R {τ}        s (case e of e₁ ∣ e₂) s′ (case e′ of e₁ ∣ e₂)

    RC-box : ∀ {s s′ e e′} →
      CtxtRel 𝒜 R         s e       s′ e′ →
      CtxtRel 𝒜 R {Box τ} s (box e) s′ (box e′)

    RC-unbox : ∀ {s s′ e e′} →
      CtxtRel 𝒜 R     s e            s′ e′ →
      CtxtRel 𝒜 R {τ} s (unbox e) s′ (unbox e′)

    RC-appl : ∀ {s s′ e e′ eₐ} →
      CtxtRel 𝒜 R {τₐ `→ τᵣ} s e        s′ e′ →
      CtxtRel 𝒜 R {τᵣ}       s (e · eₐ) s′ (e′ · eₐ)

    RC-appr : ∀ {s s′ e e′ v} →
      (iv : ATAnn 𝒜 ∣ v isvalof (τₐ `→ τᵣ)) →
      CtxtRel 𝒜 R {τₐ} s e       s′ e′ →
      CtxtRel 𝒜 R {τᵣ} s (v · e) s′ (v · e′)

    RC-unroll : ∀ {τ s s′ e e′} →
      CtxtRel 𝒜 R {μ τ} s e          s′ e′ →
      CtxtRel 𝒜 R       s (unroll e) s′ (unroll e′)

    RC-roll : ∀ {τ s s′ e e′} →
      CtxtRel 𝒜 R       s e          s′ e′ →
      CtxtRel 𝒜 R {μ τ} s (roll τ e) s′ (roll τ e′)

    RC-seq : ∀ {s s′ e e′ e₁} →
      CtxtRel 𝒜 R {τ}  s e        s′ e′ →
      CtxtRel 𝒜 R {τ₁} s (e ⨟ e₁) s′ (e′ ⨟ e₁)

data _⊢_,_⟶*_,_ (𝒯 : AnnTransit 𝒜) : ReductionRel 𝒜 where
  R-refl : ∀ {s} {e : ATAnn 𝒜 ∣ [] ⊢ τ} →
    𝒯 ⊢ s , e ⟶* s , e

  R-step : ∀ {s₁ s s′} {e₁ e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    (steps : 𝒯 ⊢ s , e ⟶* s₁ , e₁) →
    (step : 𝒯 ⊢ s₁ , e₁ ⟶ s′ , e′) →
    𝒯 ⊢ s , e ⟶* s′ , e′

map-ctxt : ∀ {Rel Rel′ : ReductionRel 𝒜} {s s′}{e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
  (∀ {τ e e′} → Rel {τ} s e s′ e′ → Rel′ s e s′ e′) →
  CtxtRel 𝒜 Rel  s e s′ e′ →
  CtxtRel 𝒜 Rel′ s e s′ e′
map-ctxt f (RC-here step)     = RC-here (f step)
map-ctxt f (RC-B step)        = RC-B (map-ctxt f step)
map-ctxt f (RC-s step)        = RC-s (map-ctxt f step)
map-ctxt f (RC-foldN step)    = RC-foldN (map-ctxt f step)
map-ctxt f (RC-assert step)   = RC-assert (map-ctxt f step)
map-ctxt f (RC-consl step)    = RC-consl (map-ctxt f step)
map-ctxt f (RC-consr iv step) = RC-consr iv (map-ctxt f step)
map-ctxt f (RC-outl step)     = RC-outl (map-ctxt f step)
map-ctxt f (RC-outr step)     = RC-outr (map-ctxt f step)
map-ctxt f (RC-inl step)      = RC-inl (map-ctxt f step)
map-ctxt f (RC-inr step)      = RC-inr (map-ctxt f step)
map-ctxt f (RC-case step)     = RC-case (map-ctxt f step)
map-ctxt f (RC-box step)      = RC-box (map-ctxt f step)
map-ctxt f (RC-unbox step)    = RC-unbox (map-ctxt f step)
map-ctxt f (RC-appl step)     = RC-appl (map-ctxt f step)
map-ctxt f (RC-appr iv step)  = RC-appr iv (map-ctxt f step)
map-ctxt f (RC-unroll step)   = RC-unroll (map-ctxt f step)
map-ctxt f (RC-roll step)     = RC-roll (map-ctxt f step)
map-ctxt f (RC-seq step)      = RC-seq (map-ctxt f step)

map-⟶ : ∀ {𝒯 : AnnTransit 𝒜} {s₁ s₂} {e₁ e₂ : ATAnn 𝒜 ∣ [] ⊢ τ} {e₁′ e₂′ : ATAnn 𝒜 ∣ [] ⊢ τ′} →
  ({Rel : ReductionRel 𝒜} → CtxtRel 𝒜 Rel s₁ e₁ s₂ e₂ → CtxtRel 𝒜 Rel s₁ e₁′ s₂ e₂′) →
  𝒯 ⊢ s₁ , e₁  ⟶ s₂ , e₂ →
  𝒯 ⊢ s₁ , e₁′ ⟶ s₂ , e₂′
map-⟶ f (R-redex step)        = R-redex (f step)
map-⟶ f (R-bdr no s₁ s₂ step) = R-bdr no s₁ s₂ (f step)

-- ∀ E → (𝒯 ⊢ s , e ⟶ s′ , e′) → (𝒯 ⊢ s , E[e] ⟶ s′ , E[e′])
step-ctxt-closed : ∀ {𝒯 : AnnTransit 𝒜} {s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
  CtxtRel 𝒜 (𝒯 ⊢_,_⟶_,_) s e s′ e′ →
  𝒯 ⊢ s , e ⟶ s′ , e′
step-ctxt-closed (RC-here step)     = step
step-ctxt-closed (RC-B step)        = map-⟶ RC-B (step-ctxt-closed step)
step-ctxt-closed (RC-s step)        = map-⟶ RC-s (step-ctxt-closed step)
step-ctxt-closed (RC-foldN step)    = map-⟶ RC-foldN (step-ctxt-closed step)
step-ctxt-closed (RC-assert step)   = map-⟶ RC-assert (step-ctxt-closed step)
step-ctxt-closed (RC-consl step)    = map-⟶ RC-consl (step-ctxt-closed step)
step-ctxt-closed (RC-consr iv step) = map-⟶ (RC-consr iv) (step-ctxt-closed step)
step-ctxt-closed (RC-outl step)     = map-⟶ RC-outl (step-ctxt-closed step)
step-ctxt-closed (RC-outr step)     = map-⟶ RC-outr (step-ctxt-closed step)
step-ctxt-closed (RC-inl step)      = map-⟶ RC-inl (step-ctxt-closed step)
step-ctxt-closed (RC-inr step)      = map-⟶ RC-inr (step-ctxt-closed step)
step-ctxt-closed (RC-case step)     = map-⟶ RC-case (step-ctxt-closed step)
step-ctxt-closed (RC-box step)      = map-⟶ RC-box (step-ctxt-closed step)
step-ctxt-closed (RC-unbox step)    = map-⟶ RC-unbox (step-ctxt-closed step)
step-ctxt-closed (RC-appl step)     = map-⟶ RC-appl (step-ctxt-closed step)
step-ctxt-closed (RC-appr iv step)  = map-⟶ (RC-appr iv) (step-ctxt-closed step)
step-ctxt-closed (RC-unroll step)   = map-⟶ RC-unroll (step-ctxt-closed step)
step-ctxt-closed (RC-roll step)     = map-⟶ RC-roll (step-ctxt-closed step)
step-ctxt-closed (RC-seq step)      = map-⟶ RC-seq (step-ctxt-closed step)

syntax ECtxt {τᵣ} Ann eᵣ {τ} e = Ann ∣ e ⦂ τ ▷ eᵣ ⦂ τᵣ
data ECtxt (Ann : AnnSig) (eᵣ : Ann ∣ [] ⊢ τᵣ) : Ann ∣ [] ⊢ τ → Set where
  E-here : ∀ {e} →
    (τᵣ≡τ : τᵣ ≡ τ) →
    (e≡eᵣ : e ≡ subst (Ann ∣ [] ⊢_) τᵣ≡τ eᵣ) →
    ECtxt Ann eᵣ {τ} e

  B#_⟪_⟫ : ∀ {e} →
    ∀ A →
    ECtxt Ann eᵣ     e →
    ECtxt Ann eᵣ {τ} (B# A ⟪ e ⟫)

  `s : ∀ {e} →
    ECtxt Ann eᵣ e →
    ECtxt Ann eᵣ (`s e)

  foldN : ∀ {e} →
    ECtxt Ann eᵣ e →
    ∀ ez es →
    ECtxt Ann eᵣ {τ} (foldN e ez es)

  assert : ∀ {e} →
    ECtxt Ann eᵣ e →
    ECtxt Ann eᵣ (assert e)

  _`,ˡ_ : ∀ {e₁} →
    ECtxt Ann eᵣ            e₁ →
    ∀ e₂ →
    ECtxt Ann eᵣ {τ₁ `* τ₂} (e₁ `, e₂)

  _`,ʳ_ : ∀ {v e} →
    (iv : Ann ∣ v isvalof τ₁) →
    ECtxt Ann eᵣ            e →
    ECtxt Ann eᵣ {τ₁ `* τ₂} (v `, e)

  π₁ : ∀ {e} →
    ECtxt Ann eᵣ {τ₁ `* τ₂} e →
    ECtxt Ann eᵣ            (π₁ e)

  π₂ : ∀ {e} →
    ECtxt Ann eᵣ {τ₁ `* τ₂} e →
    ECtxt Ann eᵣ            (π₂ e)

  inl : ∀ {e} →
    ECtxt Ann eᵣ            e →
    ECtxt Ann eᵣ {τ₁ `+ τ₂} (inl e)

  inr : ∀ {e} →
    ECtxt Ann eᵣ            e →
    ECtxt Ann eᵣ {τ₁ `+ τ₂} (inr e)

  case_of_∣_ : ∀ {e} →
    ECtxt Ann eᵣ {τ₁ `+ τ₂} e →
    ∀ e₁ e₂ →
    ECtxt Ann eᵣ {τ}        (case e of e₁ ∣ e₂)

  box : ∀ {e} →
    ECtxt Ann eᵣ         e →
    ECtxt Ann eᵣ {Box τ} (box e)

  unbox : ∀ {e} →
    ECtxt Ann eᵣ     e →
    ECtxt Ann eᵣ {τ} (unbox e)

  _·ˡ_ : ∀ {τᵣ′ e} →
    ECtxt Ann eᵣ {τₐ `→ τᵣ′} e →
    ∀ eₐ →
    ECtxt Ann eᵣ            (e · eₐ)

  _·ʳ_ : ∀ {τᵣ′ v e} →
    (iv : Ann ∣ v isvalof (τₐ `→ τᵣ′)) →
    ECtxt Ann eᵣ e →
    ECtxt Ann eᵣ (v · e)

  unroll : ∀ {τ e} →
    ECtxt Ann eᵣ {μ τ} e →
    ECtxt Ann eᵣ       (unroll e)

  roll : ∀ τ {e} →
    ECtxt Ann eᵣ e →
    ECtxt Ann eᵣ (roll τ e)

  _⨟_ : ∀ {e} →
    ECtxt Ann eᵣ {τ}  e →
    ∀ e₁ →
    ECtxt Ann eᵣ {τ′} (e ⨟ e₁)

plug-∃ : ∀ {e eᵣ eᵣ′ s s′} {Rel : ReductionRel 𝒜} →
  ATAnn 𝒜 ∣ e ⦂ τ ▷ eᵣ ⦂ τᵣ →
  Rel s eᵣ s′ eᵣ′ →
  ∃ λ e′ → CtxtRel 𝒜 Rel s e s′ e′
  -- Note: could've been stronger where e′ ≡ e[replace eᵣ by eᵣ′]
plug-∃ (E-here refl refl) step = _ , RC-here step
plug-∃ B# A ⟪ ec ⟫ step = _ , RC-B (proj₂ (plug-∃ ec step))
plug-∃ (`s ec) step = _ , RC-s (proj₂ (plug-∃ ec step))
plug-∃ (foldN ec ez es) step = _ , RC-foldN (proj₂ (plug-∃ ec step))
plug-∃ (assert ec) step = _ , RC-assert (proj₂ (plug-∃ ec step))
plug-∃ (ec `,ˡ e₂) step = _ , RC-consl (proj₂ (plug-∃ ec step))
plug-∃ (iv `,ʳ ec) step = _ , RC-consr iv (proj₂ (plug-∃ ec step))
plug-∃ (π₁ ec) step = _ , RC-outl (proj₂ (plug-∃ ec step))
plug-∃ (π₂ ec) step = _ , RC-outr (proj₂ (plug-∃ ec step))
plug-∃ (inl ec) step = _ , RC-inl (proj₂ (plug-∃ ec step))
plug-∃ (inr ec) step = _ , RC-inr (proj₂ (plug-∃ ec step))
plug-∃ (case ec of e₁ ∣ e₂) step = _ , RC-case (proj₂ (plug-∃ ec step))
plug-∃ (box ec) step = _ , RC-box (proj₂ (plug-∃ ec step))
plug-∃ (unbox ec) step = _ , RC-unbox (proj₂ (plug-∃ ec step))
plug-∃ (ec ·ˡ eₐ) step = _ , RC-appl (proj₂ (plug-∃ ec step))
plug-∃ (iv ·ʳ ec) step = _ , RC-appr iv (proj₂ (plug-∃ ec step))
plug-∃ (unroll ec) step = _ , RC-unroll (proj₂ (plug-∃ ec step))
plug-∃ (roll τ ec) step = _ , RC-roll (proj₂ (plug-∃ ec step))
plug-∃ (ec ⨟ e₁) step = _ , RC-seq (proj₂ (plug-∃ ec step))

unplug-∃ : ∀ {e e′ s s′} {Rel : ReductionRel 𝒜} →
  CtxtRel 𝒜 Rel s e s′ e′ →
  ∃ λ τᵣ → ∃₂ λ eᵣ eᵣ′ →
    ATAnn 𝒜 ∣ e ⦂ τ ▷ eᵣ ⦂ τᵣ ×
    ATAnn 𝒜 ∣ e′ ⦂ τ ▷ eᵣ′ ⦂ τᵣ ×
    Rel s eᵣ s′ eᵣ′
unplug-∃ (RC-here step)     = _ , _ , _ , E-here refl refl ,′ E-here refl refl ,′ step
unplug-∃ (RC-B step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , B# _ ⟪ ec ⟫ ,′ B# _ ⟪ ec′ ⟫ ,′ rel
unplug-∃ (RC-s step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , `s ec ,′ `s ec′ ,′ rel
unplug-∃ (RC-foldN step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , foldN ec _ _ ,′ foldN ec′ _ _ ,′ rel
unplug-∃ (RC-assert step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , assert ec ,′ assert ec′ ,′ rel
unplug-∃ (RC-consl step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , (ec `,ˡ _) ,′ (ec′ `,ˡ _) ,′ rel
unplug-∃ (RC-consr iv step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , (iv `,ʳ ec) ,′ (iv `,ʳ ec′) ,′ rel
unplug-∃ (RC-outl step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , π₁ ec ,′ π₁ ec′ ,′ rel
unplug-∃ (RC-outr step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , π₂ ec ,′ π₂ ec′ ,′ rel
unplug-∃ (RC-inl step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , inl ec ,′ inl ec′ ,′ rel
unplug-∃ (RC-inr step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , inr ec ,′ inr ec′ ,′ rel
unplug-∃ (RC-case step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , (case ec of _ ∣ _) ,′ (case ec′ of _ ∣ _) ,′ rel
unplug-∃ (RC-box step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , box ec ,′ box ec′ ,′ rel
unplug-∃ (RC-unbox step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , unbox ec ,′ unbox ec′ ,′ rel
unplug-∃ (RC-appl step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , (ec ·ˡ _) ,′ (ec′ ·ˡ _) ,′ rel
unplug-∃ (RC-appr iv step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , (iv ·ʳ ec) ,′ (iv ·ʳ ec′) ,′ rel
unplug-∃ (RC-unroll step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , unroll ec ,′ unroll ec′ ,′ rel
unplug-∃ (RC-roll step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , roll _ ec ,′ roll _ ec′ ,′ rel
unplug-∃ (RC-seq step)
  with _ , _ , _ , ec , ec′ , rel ← unplug-∃ step
  = _ , _ , _ , (ec ⨟ _) ,′ (ec′ ⨟ _) ,′ rel
