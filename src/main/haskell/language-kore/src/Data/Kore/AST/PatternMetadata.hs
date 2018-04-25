{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
module Data.Kore.AST.PatternMetadata
    ( PatternMetadata(..)
    , IsSymbolOrAlias(..)
    , ResolvedOpMetadata(..)
    , ResolvedApplicationMetadata(..)
    , getResultSort
    , getMetadataAttributes
    , getIsSymbolOrAlias
    ) where

import           Data.Kore.AST.CommonBase
import           Data.Kore.AST.Metadata

data IsSymbolOrAlias = IsSymbol | IsAlias
data ResolvedOpMetadata level op = ResolvedOpMetadata
    { resolvedOpMetadataOperation  :: op
    , resolvedOpMetadataResultSort :: Sort level
    }
data ResolvedApplicationMetadata level variable pat op = ResolvedApplicationMetadata
    { resolvedApplicationMetadataOperation       :: op
    , resolvedApplicationMetadataResultSort      :: Sort level
    , resolvedApplicationMetadataAttributes      :: Attributes pat variable
    , resolvedApplicationMetadataIsSymbolOrAlias :: IsSymbolOrAlias
    }

-- data PatternMetadata child op
--     = ResolvedApplicationMetadata child op
--     | ResolvedOpMetadata op
data PatternMetadata level variable pat op where
    AndPatternMetadata
        :: !(ResolvedOpMetadata level (And level (pat variable)))
        -> PatternMetadata level variable pat (And level (pat variable))
    ApplicationPatternMetadata
        :: !(ResolvedApplicationMetadata level variable pat (Application level (pat variable)))
        -> PatternMetadata level variable pat (Application level (pat variable))

getResultSort :: PatternMetadata level variable pat op -> Sort level
getResultSort (AndPatternMetadata m) = resolvedOpMetadataResultSort m
getResultSort (ApplicationPatternMetadata m) =
    resolvedApplicationMetadataResultSort m

getMetadataAttributes
    :: PatternMetadata level variable pat (Application level (pat variable))
    -> Attributes pat variable
getMetadataAttributes (ApplicationPatternMetadata m) =
    resolvedApplicationMetadataAttributes m

getIsSymbolOrAlias
    :: PatternMetadata level variable pat (Application level (pat variable))
    -> IsSymbolOrAlias
getIsSymbolOrAlias (ApplicationPatternMetadata m) =
    resolvedApplicationMetadataIsSymbolOrAlias m

instance Metadata (PatternMetadata level variable pat op) op where
    extractMetadataObject (AndPatternMetadata m) = resolvedOpMetadataOperation m
    extractMetadataObject (ApplicationPatternMetadata m) =
        resolvedApplicationMetadataOperation m
