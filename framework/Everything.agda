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

-- Syntaxes
import Syntax.Type
import Syntax.Term

-- Template syntaxes (for modeling reduction rules), and annotation languages
import Syntax.Template
import Annotation.Language

-- Operational semantics
import OpSemantics.Base
import OpSemantics.TypeSafety
import OpSemantics.Properties

-- Interpretations, their properties (monotonicity and soundness), and simplified proof goals
import Annotation.Interpretation
import Annotation.Interpretation.Base
import Annotation.Interpretation.MetaVar.Base
import Annotation.Interpretation.MetaVar.Predicate
import Annotation.Interpretation.MetaVar.BoundaryPredicate
import Annotation.Interpretation.MetaVar.ExpandedBoundaryPredicate
import Annotation.Interpretation.MetaVar.Extract
import Annotation.Interpretation.MetaVar.View
import Annotation.Interpretation.MetaVar
import Annotation.Interpretation.Decompose
import Annotation.Interpretation.Property

-- Soundness of interpretation
import Annotation.Soundness

-- Two example interpretations
import Example.Empty.Interpretation
import Example.ProxyVal.Interpretation

-- The trivial annotation language, and that there is an annotation projection
-- from any annotation language to the trivial language.
import Example.Unit.Annotation

-- An example annotation language: counting the number of monitor-related reduction steps
import Example.Count.Annotation
import Example.Count.NonDecreasingInterpretation

-- A simple contract annotation language which assumes that the wrappers do not accumulate
import Example.SimpleContract.ClosedAnnotation
import Example.SimpleContract.ExtensibleAnnotation
-- The corresponding progress theorem of the contract language. Since the wrappers cannot
-- accumulate, the theorem depends on the first-order interaction interpretation below.
import Example.SimpleContract.Progress

-- An example of first-order interaction between two modules.
-- The interpretation characterizes two modules that only interact through
-- a first-order value (e.g., a first-order function).
import Example.FirstOrder.FirstOrderTy
import Example.FirstOrder.FlatBoundaryExpr
import Example.FirstOrder.Interpretation

-- Findler-Felleisen contracts
import Contract.Common
import Contract.Base
import Contract.Satisfaction         -- The satisfaction relation for contracts
import Contract.Vectorized
import Contract.Monotonic            -- The non-masking property
import Contract.MonotonicStratified  -- The non-masking property, for the stratified language
import Contract.Progress             -- The full Progress theorem

-- Complete monitoring
import Blame.Base
import Blame.Ownership               -- The ownership consistency property
import Blame.Sign
import Blame.Consistency             -- The obligation consistency property
import Blame.Progress                -- The full Progress theorem, for complete monitoring

-- Space-Efficient Contracts
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
import SpaceEfficient.Equivalence.Interpretation
import SpaceEfficient.Equivalence.Soundness
import SpaceEfficient.Equivalence
