Formalization of Contract System Metatheories à la Carte: A Transition-System View of Contracts
=====
## Overview

This repository contains the Agda formalization of the proofs in the OOPSLA 2025
paper, [Contract System Metatheories à la Carte: A Transition-System View of Contracts](https://doi.org/10.1145/3764861)
by [Shu-Hung You](https://github.com/shhyou), [Christos Dimoulas](https://users.cs.northwestern.edu/~chrdimo/) and [Robby Findler](https://users.cs.northwestern.edu/~robby/).

The proofs have been checked using Agda 2.7.0.1 and the Agda Standard Library 2.2.
To type check the proofs, visit [framework/](framework/) and load [Everything.agda](framework/Everything.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Everything.html) in Emacs or Visual Studio Code.

[The HTML version is also available](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Everything.html).

## Organization of the Repository

- Section 2.1: Findler-Felleisen contracts.

  The [`Contract/`](framework/Contract/) directory contains $(\mathscr{A}\_\mathit{ctc},\mathscr{T}\_c)$, the annotation language
  that captures Findler-Felleisen contracts.
  In the code, $\kappa : \mathsf{Ctc}\\,\tau$ is the datatype, `SCtc1N` [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Contract.Base.html#1139),
  $\mathscr{A}\_\mathit{ctc}$ is called `𝒜sctc` [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Contract.Base.html#4909),
  and $\mathscr{T}\_c$ is called `𝒯sctc` [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Contract.Base.html#5742).

  The non-masking property of $\lambda\_m[\mathscr{A}\_\mathit{ctc};\mathscr{T}\_c]$ is formalized in [`Monotonic.agda`](framework/Contract/Monotonic.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Contract.Monotonic.html) and [`MonotonicStratified.agda`](framework/Contract/MonotonicStratified.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Contract.MonotonicStratified.html).
  The file [`Progress.agda`](framework/Contract/Progress.agda#L251) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Contract.Progress.html#9328) contains the full Progress theorem for the instance $\lambda_m[\mathscr{A}\_c;\mathscr{T}\_c]$.

- Section 2.2: contracts with blame.

  [`Blame/Base.agda`](framework/Blame/Base.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Base.html) formalizes the _contracts with blame_ annotation language, $(\mathscr{A}\_\mathit{bctc},\mathscr{T}\_\mathit{bc})$. In the code, $\mathscr{A}\_\mathit{bctc}$ is called  `𝒜blame` [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Base.html#1993),
  and $\mathscr{T}\_\mathit{bc}$ is just `𝒯` in [`Consistency.agda#L70`](framework/Blame/Consistency.agda#L70) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Consistency.html#2070) (and in [`Ownership.agda#L74`](framework/Blame/Ownership.agda#L74) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Ownership.html#2285), which is the same).

  It is worth noting that the blame objects and the monitor-related rules for propagating them are directly defined in `𝒜blameobj` [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Base.html#1488) and `𝒯blame` [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Base.html#3566), without any reference to contracts.
  When constructing the full monitor-related rules $\mathscr{T}\_\mathit{bc}$, the definition $\mathscr{T}$ [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Ownership.html#2285) composes `𝒯blame` and `𝒯sctc` (i.e. $\mathscr{T}\_c$) by taking their intersection.

- Section 3: the monitor calculus.

  The calculus is formalized in three parts: its [syntax](framework/Syntax/) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Syntax.Term.html#1009), [operational semantics](framework/OpSemantics/), and its parameter—[the annotation languages](framework/Annotation/Language.agda#L34) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Annotation.Language.html#838).

  The reduction relation $\longrightarrow$ is defined in [`OpSemantics/Base.agda`](framework/OpSemantics/Base.agda#L46) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/OpSemantics.Base.html#1293).
  The program-related reduction relation $\longrightarrow_p$ is `CtxtRel 𝒜 BetaRel`, and
  the monitor-related reduction relation $\longrightarrow_m$ is (approximately) `∀ tag → CtxtRel 𝒜 (Step (AnnRules Ann tag , 𝒯 tag))`. See the types of `R-redex` and `R-bdr`.

  See [the counting example](framework/Example/Count/Annotation.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Example.Count.Annotation.html) for a simple language (and the code for its monitor-related rules). Also see the simple-contract example, [`ClosedAnnotation.agda`](framework/Example/SimpleContract/ClosedAnnotation.agda#L132) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Example.SimpleContract.ClosedAnnotation.html#3660), for the actual representation of annotations. The simple-contract example is further refined in [`ExtensibleAnnotation.agda`](framework/Example/SimpleContract/ExtensibleAnnotation.agda#L139) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Example.SimpleContract.ExtensibleAnnotation.html#3783) to illustrate the use of lenses for building extensible annotation languages.

- Section 4: invariants, the satisfaction relation, and the monotonicity and soundness of invariants.

  All definitions in this section are re-exported via the [`Annotation.Invariant`](framework/Annotation/Invariant.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Annotation.Invariant.html) module.

  * Invariants and the satisfaction relation: [`Base.agda`](framework/Annotation/Invariant/Base.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Annotation.Invariant.Base.html)
  * The definition of monotonic invariants and sound invariants: [`Property.agda`](framework/Annotation/Invariant/Property.agda#L75) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Annotation.Invariant.Property.html#2394). For concrete examples, see e.g., [`NonDecreasingInvariant.agda`](framework/Example/Count/NonDecreasingInvariant.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Example.Count.NonDecreasingInvariant.html) that the register of [the counting instance](framework/Example/Count/Annotation.agda) is non-decreasing, or [`ProxyVal`](framework/Example/ProxyVal/Invariant.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Example.ProxyVal.Invariant.html) that `box`es always store values.
  * Full monotonicity and soundness: [`Soundness.agda`](framework/Annotation/Soundness.agda#L346) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Annotation.Soundness.html#14633)

- Sections 5: correct blame and complete monitoring.

  The [`Blame/`](framework/Blame/) directory contains the proofs of correct blame and complete monitoring for the instance, $\lambda_m[\mathscr{A}\_\mathit{obctc},\mathscr{T}\_\mathit{obc}]$.

  * The annotation languages: [`Base.agda`](framework/Blame/Base.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Base.html)
  * Consistency (or, obligation consistency): [`Consistency.agda`](framework/Blame/Consistency.agda#L187) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Consistency.html#6576),
    that the monitor-related rules preserve the `BlameConsistent` [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Consistency.html#2203) judgment.
  * Single-owner policy: [`Ownership.agda`](framework/Blame/Ownership.agda#L101) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Ownership.html#3132),
    that the ownership labels on the indices are lined up
    according to `BlameSeq` [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Ownership.html#2445).
  * Progress theorem, for complete monitoring: [`Progress.agda`](framework/Blame/Progress.agda#L298) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Blame.Progress.html#11726)

- Section 6: space-efficient contracts.

  The [`SpaceEfficient/`](framework/SpaceEfficient/) directory contains $\mathscr{A}\_\mathit{se}$, an annotation language that captures [Greenberg [2016]](https://doi.org/10.1007/978-3-030-14805-8_1)'s space-efficient latent contracts (excluding the dependent function contract part),
    together with its various correctness properties: the correct asymptotic complexity for space- and time-usage, and the equivalence with Findler-Felleisen contracts.

  * The annotation language: [`Base.agda`](framework/SpaceEfficient/Base.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Base.html) contains the syntax of space-efficient contracts, the definition of $\mathscr{A}\_\mathit{se}$, the `join` [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Base.html#6025) operation that merges two space-efficient contracts, and the monitor-related rules $\mathscr{T}\_\mathit{s}$. In the code, the corresponding definitions are `𝒜cctc` [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Base.html#4263) and `𝒯cctc` [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Base.html#6869), respectively.
  * Space-efficiency bounds: [`Bounded/Size.agda`](framework/SpaceEfficient/Bounded/Size.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Bounded.Size.html)
  * Time complexity bounds:
    + The annotation language, $(\mathscr{A}\_\mathit{ccs},\mathscr{T}\_\mathit{ccs})$: [`Bounded/Base.agda`](framework/SpaceEfficient/Bounded/Base.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Bounded.Base.html) defines the annotations and the register,
      and [`Bounded/OpSemantics.agda`](framework/SpaceEfficient/Bounded/OpSemantics.agda#L47) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Bounded.OpSemantics.html#1442) separately defines the monitor-related rules. In the code, the corresponding definitions are `𝒜ccctc` and `𝒯cntctc`.

      Note that `𝒯cntctc` is defined by sequentially composing `𝒯cctc` from [`Base.agda`](framework/SpaceEfficient/Base.agda#L207) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Base.html#6869), `𝒯chkcost` from [`Cost/Checking.agda`](framework/SpaceEfficient/Cost/Checking.agda#L53) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Cost.Checking.html#1618), `𝒯secost` from [`Cost/Join.agda`](framework/SpaceEfficient/Cost/Join.agda#L53) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Cost.Join.html#1612), and `𝒯cnt` from [`Count/Annotation.agda`](framework/Example/Count/Annotation.agda#L33) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/Example.Count.Annotation.html#966); each `𝒯` defines the behavior of a separate counter in the register.
    + The bounds of the number of flat-contract checks: [`CheckingCost.agda`](framework/SpaceEfficient/Bounded/CheckingCost.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Bounded.CheckingCost.html)
    + The bounds of the cost of `join` (for merging space-efficient contracts): [`JoinCost.agda`](framework/SpaceEfficient/Bounded/JoinCost.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Bounded.JoinCost.html)
  * Equivalence with $\mathscr{A}\_\mathit{ctc}$, i.e. Findler-Felleisen contract:
    + The annotation language $(\mathscr{A}\_\mathit{sctc},\mathscr{T}\_\mathit{sc})$: [`Equivalence/Base.agda`](framework/SpaceEfficient/Equivalence/Base.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Equivalence.Base.html) defines the syntax of the annotation and the register; [`Equivalence/OpSemantics.agda`](framework/SpaceEfficient/Equivalence/OpSemantics.agda#L41) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Equivalence.OpSemantics.html#1147) defines the monitor-related rules.
      In the code, the corresponding definitions are `𝒜csctc` and `𝒯csctc`.

      Just like `𝒯cntctc`, `𝒯csctc` is defined by directly composing the monitor-related rules of $\mathscr{T}\_c$ and $\mathscr{T}\_s$. There is no duplication of the definitions.
    + The ~ relation: [`Simulation.agda`](framework/SpaceEfficient/Equivalence/Simulation.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Equivalence.Simulation.html)

      In the code, [`CollapsedCtcs`](framework/SpaceEfficient/Equivalence/Simulation.agda#L191) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Equivalence.Simulation.html#7836) is the ~ relation, and [`CollapsedPreds`](framework/SpaceEfficient/Equivalence/Simulation.agda#L71) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Equivalence.Simulation.html#2528) is the ~ relation but for flat contracts.

      The file also contains the proof that `drop`, `join-flats` ($\mathit{joinp}$ in the paper), and `join` preserves ~.
    + The invariant: [`Invariant.agda`](framework/SpaceEfficient/Equivalence/Invariant.agda#L180) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Equivalence.Invariant.html#8082)
    + The monotonicity and the soundness proofs: [`Soundness.agda`](framework/SpaceEfficient/Equivalence/Soundness.agda) [[html]](https://shhyou.github.io/monitor-calculus/html/oopsla25-formalization/SpaceEfficient.Equivalence.Soundness.html)

Finally, apart from the results presented in the paper, the [example](framework/Example/) directory includes some example annotation languages and invariants.
