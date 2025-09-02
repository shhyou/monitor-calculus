{-# OPTIONS --without-K --safe #-}

module Everything where

-- Utilities, helper lemmas (about standard constructs)
import Utils.Misc
import Data.VecProperties
import Data.IsNonEmpty
import Data.NatProperties
import TransitionRelationUtil

-- The Tick monad that counts the number of operations
import Data.Tick

-- Helper for time complexity
import Data.RawFilter

-- Section 3: the monitor calculus. Syntaxes
import Syntax.Type
import Syntax.Term
-- template syntaxes (for modeling reduction rules), and annotation languages
import Syntax.Template
import Annotation.Language -- the definition of annotation language and monitor-related reduction rules
-- operational semantics
import OpSemantics.Base
import OpSemantics.TypeSafety
import OpSemantics.Properties

-- Section 4: Invariant, its properties (monotonicity and soundness), and simplified proof goals
import Annotation.Invariant
import Annotation.Invariant.Base
import Annotation.Invariant.MetaVar.Base
import Annotation.Invariant.MetaVar.Predicate
import Annotation.Invariant.MetaVar.BoundaryPredicate
import Annotation.Invariant.MetaVar.ExpandedBoundaryPredicate
import Annotation.Invariant.MetaVar.Extract
import Annotation.Invariant.MetaVar.View
import Annotation.Invariant.MetaVar
import Annotation.Invariant.Decompose
import Annotation.Invariant.Property
-- Soundness of invariant
import Annotation.Soundness

-- Two example invariants
import Example.Empty.Invariant
import Example.ProxyVal.Invariant

-- The trivial annotation language, and that there is an instance projection
-- from any annotation language to the trivial language.
import Example.Unit.Annotation

-- An example annotation language: counting the number of monitor-related reduction steps
import Example.Count.Annotation
import Example.Count.NonDecreasingInvariant

-- A simple contract annotation language which assumes that the wrappers do not accumulate
import Example.SimpleContract.ClosedAnnotation
import Example.SimpleContract.ExtensibleAnnotation
-- The corresponding progress theorem of the contract language. Since the wrappers cannot
-- accumulate, the theorem depends on the first-order interaction invariant below.
import Example.SimpleContract.Progress

-- An example of first-order interaction between two modules.
-- The invariant characterizes two modules that only interact through
-- a first-order value (e.g., a first-order function).
import Example.FirstOrder.FirstOrderTy
import Example.FirstOrder.FlatBoundaryExpr
import Example.FirstOrder.Invariant

-- Section 2: Findler-Felleisen contracts
import Contract.Common
import Contract.Base
import Contract.Satisfaction         -- The satisfaction relation for contracts
import Contract.Vectorized
import Contract.Monotonic            -- The non-masking property
import Contract.MonotonicStratified  -- The non-masking property, for the stratified annotation language
import Contract.Progress             -- The full Progress theorem

-- Section 5: Complete monitoring
import Blame.Base
import Blame.Ownership               -- The ownership consistency property
import Blame.Sign
import Blame.Consistency             -- The obligation consistency property
import Blame.Progress                -- The full Progress theorem, for complete monitoring

-- Section 6: Space-Efficient Contracts
import SpaceEfficient.OrderedPredicate
import SpaceEfficient.Base
import SpaceEfficient.Cost.Checking             -- The number of contract checks
import SpaceEfficient.Cost.Join                 -- The cost of collapsing flat contracts
import SpaceEfficient.Size
import SpaceEfficient.Height
import SpaceEfficient.Sign
import SpaceEfficient.LeafPredicate
import SpaceEfficient.TimeComplexity            -- time complexity bounds for join, joinp, and drop
import SpaceEfficient.NonRecursive
-- The preservation of various properties of the space-efficient contracts
import SpaceEfficient.Properties.NonEmpty       -- non-emptiness
import SpaceEfficient.Properties.Height         -- non-increasing of height
import SpaceEfficient.Properties.NonRecursive
import SpaceEfficient.Properties.Size           -- properties of leaf-size
import SpaceEfficient.Properties.Sublist        -- join, drop, etc. respect sublists
import SpaceEfficient.Properties.UniqueSublist  -- join, drop, etc. preserve unique sublists
-- The boundedness of contract checks and the boundedness of collapsing costs
import SpaceEfficient.Bounded.Base
import SpaceEfficient.Bounded.OpSemantics
import SpaceEfficient.Bounded.NonRecursiveHeight
import SpaceEfficient.Bounded.CheckingCost
import SpaceEfficient.Bounded.JoinCost
import SpaceEfficient.Bounded.Size
import SpaceEfficient.Bounded
-- The equivalence of space-efficient contracts and Findler-Felleisen contracts
-- via annotation-level simulation
import SpaceEfficient.Equivalence.Base
import SpaceEfficient.Equivalence.OpSemantics
import SpaceEfficient.Equivalence.Simulation
import SpaceEfficient.Equivalence.Invariant
import SpaceEfficient.Equivalence.Soundness
import SpaceEfficient.Equivalence
