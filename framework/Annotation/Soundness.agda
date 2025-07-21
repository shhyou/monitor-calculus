{-# OPTIONS --without-K --no-infer-absurd-clauses --safe #-}

module Annotation.Soundness where

open import Syntax.Type
open import Syntax.Term
open import Syntax.Template
open import OpSemantics.Base
open import Annotation.Language
open import Annotation.Interpretation
open import Annotation.Interpretation.MetaVar.Extract

open import Relation.Binary.Structures as RelStruct
  using (IsPreorder; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Data.Unit.Base using (⊤; tt)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; _×_; _,′_)

open import Data.List.Base using (List; []; _∷_; lookup)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as ListAny using (Any; here; there)

open import Function.Base using (id; _∘_)
open import Function.Bundles using (Inverse; _↔_)

private variable
  𝒜 : AnnTerm
  𝒯 : AnnTransit 𝒜

  Rel : ReductionRel 𝒜

  τ τ′ τₐ τᵣ τ₁ τ₂ : Ty

monotonicity-ctxt :
  (ℐ : AnnIntr {𝒜} 𝒯) →
  (∀ {τᵣ ix s s′} {eᵣ eᵣ′ : ATAnn 𝒜 ∣ [] ⊢ τᵣ} →
    Rel s eᵣ s′ eᵣ′ →
    (I : AIInv ℐ s) →
    ℐ ⊨[ ix ] eᵣ →
    Σ[ I′ ∈ AIInv ℐ s′ ] ℐ ⊢ (s , I) ≼ (s′ , I′)) →
  ∀ {ix s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    CtxtRel 𝒜 Rel s e s′ e′ →
    (I : AIInv ℐ s) →
    ℐ ⊨[ ix ] e →
    Σ[ I′ ∈ AIInv ℐ s′ ] ℐ ⊢ (s , I) ≼ (s′ , I′)
monotonicity-ctxt ℐ base-mono (RC-here step) inv esat =
  base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-B step) inv (B/i ix ix′ ix◁ix′ bsat esat) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-s step) inv (`s esat) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-foldN step) inv (foldN esat esatz esats) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-assert step) inv (assert esat) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-consl step) inv (esat₁ `, esat₂) =
  monotonicity-ctxt ℐ base-mono step inv esat₁
monotonicity-ctxt ℐ base-mono (RC-consr iv step) inv (esat₁ `, esat₂) =
  monotonicity-ctxt ℐ base-mono step inv esat₂
monotonicity-ctxt ℐ base-mono (RC-outl step) inv (π₁ esat) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-outr step) inv (π₂ esat) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-inl step) inv (inl esat) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-inr step) inv (inr esat) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-case step) inv (case esat of esat₁ ∣ esat₂) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-box step) inv (box esat) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-unbox step) inv (unbox esat) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-appl step) inv (esat · esatₐ) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-appr iv step) inv (esat · esatₐ) =
  monotonicity-ctxt ℐ base-mono step inv esatₐ
monotonicity-ctxt ℐ base-mono (RC-unroll step) inv (unroll esat) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-roll step) inv (roll τ esat) =
  monotonicity-ctxt ℐ base-mono step inv esat
monotonicity-ctxt ℐ base-mono (RC-seq step) inv (esat ⨟ esat₁) =
  monotonicity-ctxt ℐ base-mono step inv esat

monotonicity-bdr :
  (ℐ : AnnIntr {𝒜} 𝒯)
  (tag : RuleTag) →
  let RTr = (AnnRules (ATAnn 𝒜) tag , 𝒯 tag) in
  TransitInterpIs ℐ Monotonic tag →
  ∀ {ix s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    ATStep 𝒜 RTr s e s′ e′ →
    (I : AIInv ℐ s) →
    ℐ ⊨[ ix ] e →
    Σ[ I′ ∈ AIInv ℐ s′ ] ℐ ⊢ (s , I) ≼ (s′ , I′)
monotonicity-bdr {𝒜} ℐ tag monotonic {ix = ix} {s = s} step inv esat
  rewrite Term.subst-eq (ATStep.term₁ step)
  = monotonic step esat termSat
  where
      mvix,isSat⊨ϑ = AnnRulesExtractMetaVar 𝒜 tag (ATStep.tyvars step) esat

      mkMVIxPredView₁ = proj₁ ∘ AnnRulesMVIxPredView 𝒜 tag (ATStep.tyvars step)

      isSatIxView₁-iso = MVIxPredView.iso (mkMVIxPredView₁ IsSatIxPred)
                                          (ix , esat)
                                          (proj₁ mvix,isSat⊨ϑ)
                                          ix

      boundarySatView₁-iso = MVIxPredView.iso (mkMVIxPredView₁ BoundarySatPred)
                                              tt
                                              (proj₁ mvix,isSat⊨ϑ)
                                              ix

      termSat : TermSat ℐ mkMVIxPredView₁ (ATStep.term₁ step) esat
      TermSat.metaVarIx  termSat = proj₁ mvix,isSat⊨ϑ
      TermSat.isSatIx    termSat =
        Inverse.to isSatIxView₁-iso (proj₁ (proj₂ mvix,isSat⊨ϑ))
      TermSat.inv        termSat = inv
      TermSat.metaVarSat termSat = proj₂ (proj₂ mvix,isSat⊨ϑ)
      TermSat.boundarySat termSat =
        Inverse.to boundarySatView₁-iso (⊨⇒BoundarySat e₁ᵗ esat (proj₁ (proj₂ mvix,isSat⊨ϑ)))
        where e₁ᵗ = exprᵗ (ATStep.termTmpl₁ step)

monotonicity :
  (ℐ : AnnIntr {𝒜} 𝒯) →
  AnnTransitInterpIs ℐ Monotonic →
  ∀ {ix s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    𝒯 ⊢ s , e ⟶ s′ , e′ →
    (I : AIInv ℐ s) →
    ℐ ⊨[ ix ] e →
    Σ[ I′ ∈ AIInv ℐ s′ ] ℐ ⊢ (s , I) ≼ (s′ , I′)
monotonicity ℐ monotonic (R-redex step) inv esat =
  inv , IsPreorder.reflexive (AnnIntr.isPreorder ℐ) refl
monotonicity ℐ monotonic (R-bdr tag s s′ step) inv esat =
  monotonicity-ctxt ℐ (monotonicity-bdr ℐ tag (monotonic tag)) step inv esat




soundness′-ctxt :
  (ℐ : AnnIntr {𝒜} 𝒯) →
  (∀ {τᵣ ix s s′ eᵣ eᵣ′} →
    Rel {τᵣ} s eᵣ s′ eᵣ′ →
    (I : AIInv ℐ s) (I′ : AIInv ℐ s′) →
    ℐ ⊢ (s , I) ≼ (s′ , I′) →
    ℐ ⊨[ ix ] eᵣ →
    ℐ ⊨[ ix ] eᵣ′) →
  ∀ {ix s s′ e e′} →
    (injRel : ∀ {τ e e′}  →  CtxtRel 𝒜 Rel {τ} s e s′ e′  →  𝒯 ⊢ s , e ⟶ s′ , e′) →
    CtxtRel 𝒜 Rel {τ} s e s′ e′ →
    (I : AIInv ℐ s) (I′ : AIInv ℐ s′) →
    ℐ ⊢ (s , I) ≼ (s′ , I′) →
    ℐ ⊨[ ix ] e →
    ℐ ⊨[ ix ] e′
soundness′-ctxt ℐ base-sound injRel (RC-here step) inv inv′ mono esat =
  base-sound step inv inv′ mono esat
soundness′-ctxt ℐ base-sound injRel (RC-B step) inv inv′ mono (B/i ix ix′ ix◁ix′ bsat esat) =
  B/i _ _ ix◁ix′
      (AnnIntr.𝔹Sound ℐ (injRel step) inv inv′ mono bsat)
      (soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat)
soundness′-ctxt ℐ base-sound injRel (RC-s step) inv inv′ mono (`s esat) =
  `s (soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat)
soundness′-ctxt ℐ base-sound injRel (RC-foldN step) inv inv′ mono (foldN esat esatz esats) =
  foldN (soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat)
        esatz
        esats
soundness′-ctxt ℐ base-sound injRel (RC-assert step) inv inv′ mono (assert esat) =
  assert (soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat)
soundness′-ctxt ℐ base-sound injRel (RC-consl step) inv inv′ mono (esat₁ `, esat₂) =
  soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat₁ `,
  esat₂
soundness′-ctxt ℐ base-sound injRel (RC-consr iv step) inv inv′ mono (esat₁ `, esat₂) =
  esat₁ `,
  soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat₂
soundness′-ctxt ℐ base-sound injRel (RC-outl step) inv inv′ mono (π₁ esat) =
  π₁ (soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat)
soundness′-ctxt ℐ base-sound injRel (RC-outr step) inv inv′ mono (π₂ esat) =
  π₂ (soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat)
soundness′-ctxt ℐ base-sound injRel (RC-inl step) inv inv′ mono (inl esat) =
  inl (soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat)
soundness′-ctxt ℐ base-sound injRel (RC-inr step) inv inv′ mono (inr esat) =
  inr (soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat)
soundness′-ctxt ℐ base-sound injRel (RC-case step) inv inv′ mono (case esat of esat₁ ∣ esat₂) =
  case soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat of
    esat₁
  ∣ esat₂
soundness′-ctxt ℐ base-sound injRel (RC-box step) inv inv′ mono (box esat) =
  box (soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat)
soundness′-ctxt ℐ base-sound injRel (RC-unbox step) inv inv′ mono (unbox esat) =
  unbox (soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat)
soundness′-ctxt ℐ base-sound injRel (RC-appl step) inv inv′ mono (esat · esatₐ) =
  soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat ·
  esatₐ
soundness′-ctxt ℐ base-sound injRel (RC-appr iv step) inv inv′ mono (esat · esatₐ) =
  esat ·
  soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esatₐ
soundness′-ctxt ℐ base-sound injRel (RC-unroll step) inv inv′ mono (unroll esat) =
  unroll (soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat)
soundness′-ctxt ℐ base-sound injRel (RC-roll step) inv inv′ mono (roll τ esat) =
  roll τ (soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat)
soundness′-ctxt ℐ base-sound injRel (RC-seq step) inv inv′ mono (esat ⨟ esat₁) =
  soundness′-ctxt ℐ base-sound injRel step inv inv′ mono esat ⨟
  esat₁

soundness′-beta′ :
  (ℐ : AnnIntr {𝒜} 𝒯) →
  ∀ {ix} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    (s : ATState 𝒜) →
    BetaRel s e s e′ →
    ℐ ⊨[ ix ] e →
    ℐ ⊨[ ix ] e′
soundness′-beta′ ℐ s R-foldz (foldN esat esatz esats) = esatz
soundness′-beta′ ℐ s (R-folds iv) (foldN (`s esat) esatz esats) =
  isubst esats [i0↦ esat &&i1↦ foldN esat esatz esats ]
soundness′-beta′ ℐ s (R-assert iv) (assert esat) = ⋆
soundness′-beta′ ℐ s (R-outl iv₁ iv₂) (π₁ (esat₁ `, esat₂)) = esat₁
soundness′-beta′ ℐ s (R-outr iv₁ iv₂) (π₂ (esat₁ `, esat₂)) = esat₂
soundness′-beta′ ℐ s (R-casel iv) (case (inl esat) of esat₁ ∣ esat₂) =
  isubst esat₁ [i0↦ esat ]
soundness′-beta′ ℐ s (R-caser iv) (case (inr esat) of esat₁ ∣ esat₂) =
  isubst esat₂ [i0↦ esat ]
soundness′-beta′ ℐ s (R-unbox x) (unbox (box esat)) = esat
soundness′-beta′ ℐ s (R-β iv) ((ƛ esat) · esatₐ) =
  isubst esat [i0↦ esatₐ ]
soundness′-beta′ ℐ s (R-unroll iv) (unroll (roll τ esat)) = esat
soundness′-beta′ ℐ s R-fix (fix esat) =
  isubst esat [i0↦ fix esat ]
soundness′-beta′ ℐ s (R-seq iv) (esat ⨟ esat₁) = esat₁

soundness′-beta :
  (ℐ : AnnIntr {𝒜} 𝒯) →
  ∀ {ix s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    (BetaRel s e s′ e′) →
    (I : AIInv ℐ s) (I′ : AIInv ℐ s′) →
    ℐ ⊢ (s , I) ≼ (s′ , I′) →
    ℐ ⊨[ ix ] e →
    ℐ ⊨[ ix ] e′
soundness′-beta ℐ {s = s} step inv inv′ mono esat =
  soundness′-beta′ ℐ s step esat

soundness′-bdr :
  (ℐ : AnnIntr {𝒜} 𝒯)
  (tag : RuleTag) →
  let RTr = AnnRules (ATAnn 𝒜) tag , 𝒯 tag in
  TransitInterpIs ℐ Sound tag →
  ∀ {ix s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    ATStep 𝒜 RTr s e s′ e′ →
    (I : AIInv ℐ s) (I′ : AIInv ℐ s′) →
    ℐ ⊢ (s , I) ≼ (s′ , I′) →
    ℐ ⊨[ ix ] e →
    ℐ ⊨[ ix ] e′
soundness′-bdr {𝒜} ℐ tag sound {ix = ix} {s = s} {s′ = s′} step inv inv′ mono esat
  rewrite Term.subst-eq (ATStep.term₁ step) | Term.subst-eq (ATStep.term₂ step)
  = isubstᵗ (exprᵗ (ATStep.termTmpl₂ step))
            (TermSat.metaVarSat termSat)
            (Inverse.from isTermIxView₂-iso (SoundSat.isTermIx ⊨sound))
            (Inverse.from boundarySatView₂-iso (SoundSat.boundarySat ⊨sound))
  where
      mvix,isSat⊨ϑ = AnnRulesExtractMetaVar 𝒜 tag (ATStep.tyvars step) esat

      mkMVIxPredView₁ = proj₁ ∘ AnnRulesMVIxPredView 𝒜 tag (ATStep.tyvars step)
      mkMVIxPredView₂ = proj₂ ∘ AnnRulesMVIxPredView 𝒜 tag (ATStep.tyvars step)

      isSatIxView₁-iso = MVIxPredView.iso (mkMVIxPredView₁ IsSatIxPred)
                                          (ix , esat)
                                          (proj₁ mvix,isSat⊨ϑ)
                                          ix

      boundarySatView₁-iso = MVIxPredView.iso (mkMVIxPredView₁ BoundarySatPred)
                                              tt
                                              (proj₁ mvix,isSat⊨ϑ)
                                              ix

      termSat : TermSat ℐ mkMVIxPredView₁ (ATStep.term₁ step) esat
      TermSat.metaVarIx  termSat = proj₁ mvix,isSat⊨ϑ
      TermSat.isSatIx    termSat =
        Inverse.to isSatIxView₁-iso (proj₁ (proj₂ mvix,isSat⊨ϑ))
      TermSat.inv        termSat = inv
      TermSat.metaVarSat termSat = proj₂ (proj₂ mvix,isSat⊨ϑ)
      TermSat.boundarySat termSat =
        Inverse.to boundarySatView₁-iso (⊨⇒BoundarySat e₁ᵗ esat (proj₁ (proj₂ mvix,isSat⊨ϑ)))
        where e₁ᵗ = exprᵗ (ATStep.termTmpl₁ step)

      ⊨sound = sound step esat termSat (inv′ , mono)

      isTermIxView₂-iso = MVIxPredView.iso (mkMVIxPredView₂ IsTermIxPred)
                                            tt
                                            (SoundSat.metaVarIx ⊨sound)
                                            ix

      boundarySatView₂-iso = MVIxPredView.iso (mkMVIxPredView₂ BoundarySatPred)
                                              tt
                                              (SoundSat.metaVarIx ⊨sound)
                                              ix

soundness′ :
  (ℐ : AnnIntr {𝒜} 𝒯) →
  AnnTransitInterpIs ℐ Sound →
  ∀ {ix s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    (step : 𝒯 ⊢ s , e ⟶ s′ , e′) →
    (I  : AIInv ℐ s) (I′ : AIInv ℐ s′) →
    ℐ ⊢ (s , I) ≼ (s′ , I′) →
    ℐ ⊨[ ix ] e →
    ℐ ⊨[ ix ] e′
soundness′ ℐ sound (R-redex step) inv inv′ mono esat =
  soundness′-ctxt ℐ (soundness′-beta ℐ) R-redex step inv inv′ mono esat
soundness′ ℐ sound (R-bdr tag s s′ step) inv inv′ mono esat =
  soundness′-ctxt ℐ (soundness′-bdr ℐ tag (sound tag)) (R-bdr tag s s′) step inv inv′ mono esat

soundness :
  (ℐ : AnnIntr {𝒜} 𝒯) →
  AnnTransitInterpIs ℐ Monotonic →
  AnnTransitInterpIs ℐ Sound →
  ∀ {ix s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
    (step : 𝒯 ⊢ s , e ⟶ s′ , e′) →
    AIInv ℐ s →
    ℐ ⊨[ ix ] e →
    ℐ ⊨[ ix ] e′
soundness ℐ monotonic sound step inv esat =
  soundness′ ℐ sound step inv (proj₁ inv′,s≼s′) (proj₂ inv′,s≼s′) esat
  where inv′,s≼s′ = monotonicity ℐ monotonic step inv esat

mutual
  monotonicity* :
    (ℐ : AnnIntr {𝒜} 𝒯) →
    AnnTransitInterpIs ℐ Monotonic →
    AnnTransitInterpIs ℐ Sound →
    ∀ {ix s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
      𝒯 ⊢ s , e ⟶* s′ , e′ →
      (I : AIInv ℐ s) →
      ℐ ⊨[ ix ] e →
      Σ[ I′ ∈ AIInv ℐ s′ ] ℐ ⊢ (s , I) ≼ (s′ , I′)
  monotonicity* ℐ monotonic sound R-refl inv esat =
    inv , IsPreorder.reflexive (AnnIntr.isPreorder ℐ) refl
  monotonicity* ℐ monotonic sound (R-step steps step) inv esat =
    proj₁ inv′,s₁≼s′ ,
    IsPreorder.trans (AnnIntr.isPreorder ℐ) (proj₂ inv₁,s≼s₁) (proj₂ inv′,s₁≼s′)
    where inv₁,s≼s₁ = monotonicity* ℐ monotonic sound steps inv esat
          esat₁ = soundness* ℐ monotonic sound steps inv esat
          inv′,s₁≼s′ = monotonicity ℐ monotonic step (proj₁ inv₁,s≼s₁) esat₁

  soundness* :
    (ℐ : AnnIntr {𝒜} 𝒯) →
    AnnTransitInterpIs ℐ Monotonic →
    AnnTransitInterpIs ℐ Sound →
    ∀ {ix s s′} {e e′ : ATAnn 𝒜 ∣ [] ⊢ τ} →
      (step : 𝒯 ⊢ s , e ⟶* s′ , e′) →
      AIInv ℐ s →
      ℐ ⊨[ ix ] e →
      ℐ ⊨[ ix ] e′
  soundness* ℐ monotonic sound R-refl inv esat = esat
  soundness* ℐ monotonic sound (R-step steps step) inv esat =
    soundness ℐ monotonic sound step (proj₁ inv₁,s≼s₁) esat₁
    where inv₁,s≼s₁ = monotonicity* ℐ monotonic sound steps inv esat
          esat₁ = soundness* ℐ monotonic sound steps inv esat
