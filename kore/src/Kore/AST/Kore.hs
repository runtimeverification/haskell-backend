{-|
Module      : Kore.AST.Kore
Description : Data Structures for representing the Kore language AST with
              unified constructs.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module includes all the data structures necessary for representing
the syntactic categories of a Kore definition that need unified
constructs.

Unified constructs are those that represent both meta and object versions of
an AST term in a single data type (e.g. 'UnifiedSort' that can be either
'Sort Object' or 'Sort Meta')

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.AST.Kore
    ( KorePattern
    , CommonKorePattern
    , VerifiedKorePattern
    , eraseAnnotations
    , asCommonKorePattern
    -- * Re-exports
    , Base, CofreeF (..)
    , module Kore.AST.Common
    , module Kore.AST.Identifier
    , module Kore.AST.MetaOrObject
    , module Kore.Annotation.Valid
    , module Kore.Sort
    ) where

import qualified Kore.Annotation.Null as Annotation
import           Kore.Annotation.Valid
import           Kore.AST.Common hiding
                 ( castVoidDomainValues, mapDomainValues, mapVariables,
                 traverseVariables )
import           Kore.AST.Identifier
import           Kore.AST.MetaOrObject
import           Kore.AST.Pure
import qualified Kore.Domain.Builtin as Domain
import           Kore.Sort

type KorePattern = PurePattern Object

-- | View a 'Meta' or 'Object' 'Pattern' as a 'KorePattern'
asCommonKorePattern
    :: Pattern Object Domain.Builtin Variable CommonKorePattern
    -> CommonKorePattern
asCommonKorePattern pat = asPurePattern (mempty :< pat)

-- |'CommonKorePattern' is the instantiation of 'KorePattern' with common
-- 'Variable's.
type CommonKorePattern =
    KorePattern Domain.Builtin Variable (Annotation.Null Object)

-- | A 'CommonKorePattern' that has passed verification.
type VerifiedKorePattern =
    KorePattern Domain.Builtin Variable (Valid (Variable Object) Object)
