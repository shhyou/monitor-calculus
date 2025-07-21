{-# OPTIONS --without-K --no-infer-absurd-clauses --safe #-}

module Annotation.Interpretation.Base where

open import Syntax.Type
open import Syntax.Term
open import OpSemantics.Base
open import Annotation.Language

open import Relation.Binary
  using (IsEquivalence; IsPreorder; _Respects_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Function.Base using (_∋_)

open import Data.Unit.Base as Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

private variable
  𝒜 : AnnTerm
  𝒯 : AnnTransit 𝒜
  Γ Γ′ : Ctxt
  τ τ′ τₐ τᵣ τ₁ τ₂ : Ty

record AnnIntr (𝒯 : AnnTransit 𝒜) : Set₁ where
  inductive; no-eta-equality
  open AnnTerm 𝒜
  field
    Ix : Set
    IxRel : ∀ {τ} → Ann τ → Ix → Ix → Set

    Inv : State → Set

    Ord : Σ State Inv → Σ State Inv → Set
    isPreorder : IsPreorder _≡_ Ord

    𝔹 : ∀ {τ} →
      (A : Ann τ) →
      ∀ {ix ix′} → IxRel A ix ix′ →
      (e : Ann ∣ [] ⊢ τ) →
      Set
    𝔹Sound : ∀ {s s′ τ A ix ix′} {ix◁ix′ : IxRel A ix ix′} {e e′ : Ann ∣ [] ⊢ τ} →
      𝒯 ⊢ s , e ⟶ s′ , e′ →
      (I : Inv s) (I′ : Inv s′) →
      Ord (s , I) (s′ , I′) →
      𝔹 A ix◁ix′ e → 𝔹 A ix◁ix′ e′

    ℙ : ∀ {τ e} →
      (A : Ann τ) →
      ∀ {ix ix′} → IxRel A ix ix′ →
      (em : Ann ∣ e ismonctorof τ) →
      Set
open AnnIntr public using () renaming (Ix to AIIx; IxRel to AIIxRel; Inv to AIInv)

_,_⊢_◁_ : (ℐ : AnnIntr {𝒜} 𝒯) →
  ∀ {τ} → ATAnn 𝒜 τ → AIIx ℐ → AIIx ℐ → Set
ℐ , A ⊢ ix₁ ◁ ix₂ = AnnIntr.IxRel ℐ A ix₁ ix₂

_⊢_≼_ : (ℐ : AnnIntr {𝒜} 𝒯) →
  Σ (ATState 𝒜) (AIInv ℐ) → Σ (ATState 𝒜) (AIInv ℐ) → Set
ℐ ⊢ invs ≼ invs′ = AnnIntr.Ord ℐ invs invs′

𝔹_⟦_,_,_,_⟧ : ∀ (ℐ : AnnIntr {𝒜} 𝒯) τ → let open AnnTerm 𝒜 in
  (A : Ann τ) →
  ∀ {ix ix′} → AIIxRel ℐ A ix ix′ →
  Ann ∣ [] ⊢ τ →
  Set
𝔹 ℐ ⟦ τ , A , ix◁ix′ , e ⟧ = AnnIntr.𝔹 ℐ {τ} A ix◁ix′ e

ℙ_⟦_,_,_,_⟧ : ∀ (ℐ : AnnIntr {𝒜} 𝒯) τ {e} → let open AnnTerm 𝒜 in
  (A : Ann τ) →
  ∀ {ix ix′} → AIIxRel ℐ A ix ix′ →
  (em : Ann ∣ e ismonctorof τ) →
  Set
ℙ ℐ ⟦ τ , A , ix◁ix′ , em ⟧ = AnnIntr.ℙ ℐ {τ} A ix◁ix′ em

mutual
  data _⊨[_]_ (ℐ : AnnIntr {𝒜} 𝒯) :
    (ix : AIIx ℐ) → (e : ATAnn 𝒜 ∣ Γ ⊢ τ) → Set where
      proxy/i : ∀ {A e} →
        (em : ATAnn 𝒜 ∣ e ismonctorof τ) →
        ∀ ix ix′ →
        (ix◁ix′ : AIIxRel ℐ A ix ix′) →
        (psat : ℙ ℐ ⟦ τ , A , ix◁ix′ , em ⟧) →
        ℐ ⊨[ ix′ ] e →
        -------------------------------------------------
        ℐ ⊨[ ix ] ((ATAnn 𝒜 ∣ Γ ⊢ τ)  ∋  proxy A em)

      B/i : ∀ {A e} →
        ∀ ix ix′ →
        (ix◁ix′ : AIIxRel ℐ A ix ix′) →
        (bsat : 𝔹 ℐ ⟦ τ , A , ix◁ix′ , e ⟧) →
        ℐ ⊨[ ix′ ] e →
        -------------------------------------------------
        ℐ ⊨[ ix ] ((ATAnn 𝒜 ∣ Γ ⊢ τ)  ∋  B# A ⟪ e ⟫)

      ⋆ : ∀ {ix} → ℐ ⊨[ ix ] ((ATAnn 𝒜 ∣ Γ ⊢ `1)  ∋  ⋆)

      `z : ∀ {ix} → ℐ ⊨[ ix ] ((ATAnn 𝒜 ∣ Γ ⊢ `ℕ)  ∋  `z)

      `s : ∀ {ix} {e : ATAnn 𝒜 ∣ Γ ⊢ `ℕ} →
        ℐ ⊨[ ix ] e →
        -------------------
        ℐ ⊨[ ix ] `s e

      foldN : ∀ {ix e} {ez : ATAnn 𝒜 ∣ Γ ⊢ τ} {es : ATAnn 𝒜 ∣ `ℕ ∷ τ ∷ Γ ⊢ τ} →
        ℐ ⊨[ ix ] e →
        ℐ ⊨[ ix ] ez →
        ℐ ⊨[ ix ] es →
        ----------------------------
        ℐ ⊨[ ix ] foldN e ez es

      assert : ∀ {ix e} →
        ℐ ⊨[ ix ] e →
        ------------------------------------------
        ℐ ⊨[ ix ] ((ATAnn 𝒜 ∣ Γ ⊢ `1)  ∋  assert e)

      _`,_ : ∀ {ix} {e₁ : ATAnn 𝒜 ∣ Γ ⊢ τ₁} {e₂ : ATAnn 𝒜 ∣ Γ ⊢ τ₂} →
        ℐ ⊨[ ix ] e₁ →
        ℐ ⊨[ ix ] e₂ →
        -------------------------
        ℐ ⊨[ ix ] (e₁ `, e₂)

      π₁ : ∀ {ix} {e : ATAnn 𝒜 ∣ Γ ⊢ τ₁ `* τ₂} →
        ℐ ⊨[ ix ] e →
        -------------------
        ℐ ⊨[ ix ] π₁ e

      π₂ : ∀ {ix} {e : ATAnn 𝒜 ∣ Γ ⊢ τ₁ `* τ₂} →
        ℐ ⊨[ ix ] e →
        -------------------
        ℐ ⊨[ ix ] π₂ e

      inl :  ∀ {ix e} →
        ℐ ⊨[ ix ] e →
        ------------------------------------------------------
        ℐ ⊨[ ix ] ((ATAnn 𝒜 ∣ Γ ⊢ (τ₁ `+ τ₂))  ∋  inl e)

      inr :  ∀ {ix e} →
        ℐ ⊨[ ix ] e →
        -----------------------------------------------------
        ℐ ⊨[ ix ] ((ATAnn 𝒜 ∣ Γ ⊢ (τ₁ `+ τ₂))  ∋  inr e)

      case_of_∣_ : ∀ {ix e} {e₁ : ATAnn 𝒜 ∣ τ₁ ∷ Γ ⊢ τ} {e₂ : ATAnn 𝒜 ∣ τ₂ ∷ Γ ⊢ τ} →
        ℐ ⊨[ ix ] e →
        ℐ ⊨[ ix ] e₁ →
        ℐ ⊨[ ix ] e₂ →
        ----------------------------------
        ℐ ⊨[ ix ] (case e of e₁ ∣ e₂)

      box : ∀ {ix} {e : ATAnn 𝒜 ∣ Γ ⊢ τ} →
        ℐ ⊨[ ix ] e →
        --------------------
        ℐ ⊨[ ix ] box e

      unbox : ∀ {ix} {e : ATAnn 𝒜 ∣ Γ ⊢ Box τ} →
        ℐ ⊨[ ix ] e →
        ----------------------
        ℐ ⊨[ ix ] unbox e

      `_ : ∀ {ix} →
        (y : τ ∈ Γ) →
        ------------------
        ℐ ⊨[ ix ] ` y

      ƛ_ : ∀ {ix} {e : ATAnn 𝒜 ∣ τₐ ∷ Γ ⊢ τᵣ} →
        ℐ ⊨[ ix ] e →
        -------------------
        ℐ ⊨[ ix ] (ƛ e)

      _·_ : ∀ {ix eₐ} {e : ATAnn 𝒜 ∣ Γ ⊢ τₐ `→ τᵣ} →
        ℐ ⊨[ ix ] e →
        ℐ ⊨[ ix ] eₐ →
        --------------------
        ℐ ⊨[ ix ] e · eₐ

      unroll : ∀ {τ ix} {e : ATAnn 𝒜 ∣ Γ ⊢ μ τ} →
        ℐ ⊨[ ix ] e →
        -----------------------
        ℐ ⊨[ ix ] unroll e

      roll : ∀ τ {ix} {e : ATAnn 𝒜 ∣ Γ ⊢ tsubst τ [t0↦ μ τ ]} →
        ℐ ⊨[ ix ] e →
        -----------------------
        ℐ ⊨[ ix ] roll τ e

      fix : ∀ {ix} {e : ATAnn 𝒜 ∣ τ ∷ Γ ⊢ τ} →
        ℐ ⊨[ ix ] e →
        --------------------
        ℐ ⊨[ ix ] fix e

      _⨟_ : ∀ {ix} {e : ATAnn 𝒜 ∣ Γ ⊢ τ} {e₁ : ATAnn 𝒜 ∣ Γ ⊢ τ₁} →
        ℐ ⊨[ ix ] e →
        ℐ ⊨[ ix ] e₁ →
        ----------------------
        ℐ ⊨[ ix ] (e ⨟ e₁)

⌊_⌋i : ∀ {ℐ : AnnIntr {𝒜} 𝒯} {e : ATAnn 𝒜 ∣ Γ ⊢ τ} {ix} →
  ℐ ⊨[ ix ] e  →  ATAnn 𝒜 ∣ Γ ⊢ τ
⌊_⌋i {e = e} esat = e

i0mapsto [i0↦_] : ∀ {ℐ : AnnIntr {𝒜} 𝒯} {ix} {e : ATAnn 𝒜 ∣ Γ ⊢ τ} →
  ℐ ⊨[ ix ] e → ∀ {τ′} → (y : τ′ ∈ (τ ∷ Γ)) → ℐ ⊨[ ix ] x0mapsto e y
i0mapsto esat (here refl)  = esat
i0mapsto esat (there τ′∈Γ) = ` τ′∈Γ
[i0↦_] = i0mapsto

i0i1mapsto [i0↦_&&i1↦_] : ∀ {ℐ : AnnIntr {𝒜} 𝒯} {ix}
  {e : ATAnn 𝒜 ∣ Γ ⊢ τ} →
  ℐ ⊨[ ix ] e →
  {e′ : ATAnn 𝒜 ∣ Γ ⊢ τ′} →
  ℐ ⊨[ ix ] e′ →
  ∀ {τ″} → (y : τ″ ∈ (τ ∷ τ′ ∷ Γ)) →
  ℐ ⊨[ ix ] x0x1mapsto e e′ y
i0i1mapsto i0 i1 (here refl) = i0
i0i1mapsto i0 i1 (there (here refl)) = i1
i0i1mapsto i0 i1 (there (there τ″∈Γ)) = ` τ″∈Γ
[i0↦_&&i1↦_] = i0i1mapsto

irename : ∀ {ℐ : AnnIntr {𝒜} 𝒯} {ix} →
  {e : ATAnn 𝒜 ∣ Γ ⊢ τ} →
  ℐ ⊨[ ix ] e →
  (ren : ∀ {τ} → τ ∈ Γ → τ ∈ Γ′) →
  ℐ ⊨[ ix ] erename e ren
irename (proxy/i em ix ix′ ix◁ix′ psat e) ren = proxy/i em ix ix′ ix◁ix′ psat e
irename (B/i ix ix′ ix◁ix′ bsat e) ren = B/i ix ix′ ix◁ix′ bsat e
irename ⋆ ren = ⋆
irename `z ren = `z
irename (`s e) ren = `s (irename e ren)
irename (foldN e ez es) ren = foldN (irename e ren) (irename ez ren) (irename es (pext (pext ren)))
irename (assert e) ren = assert (irename e ren)
irename (e₁ `, e₂) ren = irename e₁ ren `, irename e₂ ren
irename (π₁ e) ren = π₁ (irename e ren)
irename (π₂ e) ren = π₂ (irename e ren)
irename (inl e) ren = inl (irename e ren)
irename (inr e) ren = inr (irename e ren)
irename (case e of e₁ ∣ e₂) ren = case irename e ren of irename e₁ (pext ren) ∣ irename e₂ (pext ren)
irename (box e) ren = box (irename e ren)
irename (unbox e) ren = unbox (irename e ren)
irename (` y) ren = ` ren y
irename (ƛ e) ren = ƛ (irename e (pext ren))
irename (e · eₐ) ren = irename e ren · irename eₐ ren
irename (unroll e) ren = unroll (irename e ren)
irename (roll τ e) ren = roll τ (irename e ren)
irename (fix e) ren = fix (irename e (pext ren))
irename (e ⨟ e₁) ren = irename e ren ⨟ irename e₁ ren

iext : ∀ {ℐ : AnnIntr {𝒜} 𝒯} {ix} →
  {σ : ∀ {τ′} → τ′ ∈ Γ → ATAnn 𝒜 ∣ Γ′ ⊢ τ′} →
  (∀ {τ′} → (y : τ′ ∈ Γ) → ℐ ⊨[ ix ] σ y) →
  ∀ {τ′} → (y : τ′ ∈ τ ∷ Γ) → ℐ ⊨[ ix ] eext σ y
iext ⊨σ (here refl) = ` here refl
iext ⊨σ (there τ∈Γ) = irename (⊨σ τ∈Γ) there

isubst : ∀ {ℐ : AnnIntr {𝒜} 𝒯} {ix} →
    {e : ATAnn 𝒜 ∣ Γ ⊢ τ} →
    {σ : ∀ {τ′} → τ′ ∈ Γ → ATAnn 𝒜 ∣ Γ′ ⊢ τ′} →
    ℐ ⊨[ ix ] e →
    (⊨σ : ∀ {τ′} → (y : τ′ ∈ Γ) → ℐ ⊨[ ix ] σ y) →
    ℐ ⊨[ ix ] esubst e σ
isubst (proxy/i em ix ix′ ix◁ix′ psat e) ⊨σ = proxy/i em ix ix′ ix◁ix′ psat e
isubst (B/i ix ix′ ix◁ix′ bsat e) ⊨σ = B/i ix ix′ ix◁ix′ bsat e
isubst ⋆ ⊨σ = ⋆
isubst `z ⊨σ = `z
isubst (`s e) ⊨σ = `s (isubst e ⊨σ)
isubst (foldN e ez es) ⊨σ = foldN (isubst e ⊨σ) (isubst ez ⊨σ) (isubst es (iext (iext ⊨σ)))
isubst (assert e) ⊨σ = assert (isubst e ⊨σ)
isubst (e₁ `, e₂) ⊨σ = isubst e₁ ⊨σ `, isubst e₂ ⊨σ
isubst (π₁ e) ⊨σ = π₁ (isubst e ⊨σ)
isubst (π₂ e) ⊨σ = π₂ (isubst e ⊨σ)
isubst (inl e) ⊨σ = inl (isubst e ⊨σ)
isubst (inr e) ⊨σ = inr (isubst e ⊨σ)
isubst (case e of e₁ ∣ e₂) ⊨σ = case isubst e ⊨σ of isubst e₁ (iext ⊨σ) ∣ isubst e₂ (iext ⊨σ)
isubst (box e) ⊨σ = box (isubst e ⊨σ)
isubst (unbox e) ⊨σ = unbox (isubst e ⊨σ)
isubst (` y) ⊨σ = ⊨σ y
isubst (ƛ e) ⊨σ = ƛ (isubst e (iext ⊨σ))
isubst (e · eₐ) ⊨σ = isubst e ⊨σ · isubst eₐ ⊨σ
isubst (unroll e) ⊨σ = unroll (isubst e ⊨σ)
isubst (roll τ e) ⊨σ = roll τ (isubst e ⊨σ)
isubst (fix e) ⊨σ = fix (isubst e (iext ⊨σ))
isubst (e ⨟ e₁) ⊨σ = isubst e ⊨σ ⨟ isubst e₁ ⊨σ

relabel-nat-val : ∀ {𝒜 𝒯} {ℐ : AnnIntr {𝒜} 𝒯} {ix ix′ n} →
  (iv  :  ATAnn 𝒜  ∣  n isvalof `ℕ) →
  ℐ ⊨[ ix ] n →
  ℐ ⊨[ ix′ ] n
relabel-nat-val (proxy/v A ()) _
relabel-nat-val z/v            _         = `z
relabel-nat-val (s/v iv)       (`s nsat) = `s (relabel-nat-val iv nsat)

idecompose-by-ectxt : ∀ {ℐ : AnnIntr {𝒜} 𝒯} {ix e eᵣ} →
  (ec : ATAnn 𝒜 ∣ e ⦂ τ ▷ eᵣ ⦂ τᵣ) →
  ℐ ⊨[ ix ] e →
  ∃[ ix′ ] ℐ ⊨[ ix′ ] eᵣ
idecompose-by-ectxt (E-here refl refl) e = _ , e
idecompose-by-ectxt (B# A ⟪ ec ⟫) (B/i ix ix′ ix◁ix′ bsat e) = idecompose-by-ectxt ec e
idecompose-by-ectxt (`s ec) (`s e) = idecompose-by-ectxt ec e
idecompose-by-ectxt (foldN ec ez es) (foldN e ez′ es′) = idecompose-by-ectxt ec e
idecompose-by-ectxt (assert ec) (assert e) = idecompose-by-ectxt ec e
idecompose-by-ectxt (ec `,ˡ e₂) (e₁′ `, e₂′) = idecompose-by-ectxt ec e₁′
idecompose-by-ectxt (iv `,ʳ ec) (e₁′ `, e₂′) = idecompose-by-ectxt ec e₂′
idecompose-by-ectxt (π₁ ec) (π₁ e) = idecompose-by-ectxt ec e
idecompose-by-ectxt (π₂ ec) (π₂ e) = idecompose-by-ectxt ec e
idecompose-by-ectxt (inl ec) (inl e) = idecompose-by-ectxt ec e
idecompose-by-ectxt (inr ec) (inr e) = idecompose-by-ectxt ec e
idecompose-by-ectxt (case ec of e₁ ∣ e₂) (case e of e₁′ ∣ e₂′) = idecompose-by-ectxt ec e
idecompose-by-ectxt (box ec) (box e) = idecompose-by-ectxt ec e
idecompose-by-ectxt (unbox ec) (unbox e) = idecompose-by-ectxt ec e
idecompose-by-ectxt (ec ·ˡ eₐ) (e · eₐ′) = idecompose-by-ectxt ec e
idecompose-by-ectxt (iv ·ʳ ec) (e · eₐ′) = idecompose-by-ectxt ec eₐ′
idecompose-by-ectxt (unroll ec) (unroll e) = idecompose-by-ectxt ec e
idecompose-by-ectxt (roll τ ec) (roll .τ e) = idecompose-by-ectxt ec e
idecompose-by-ectxt (ec ⨟ e₁) (e ⨟ e₁′) = idecompose-by-ectxt ec e
