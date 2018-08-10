{-# OPTIONS_GHC -fno-warn-orphans #-}
{-|
Module      : Kore.Building.Patterns
Description : Builders for the standard Kore patterns, without 'Application'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Building.Patterns where

import Data.Proxy
       ( Proxy (Proxy) )

import Kore.AST.Common
       ( And (..), AstLocation, Bottom (..), Ceil (..), CharLiteral (..),
       DomainValue (..), Equals (..), Exists (..), Floor (..), Forall (..),
       Id (..), Iff (..), Implies (..), In (..), Next (..), Not (..), Or (..),
       Pattern (..), Rewrites (..), StringLiteral (..), Top (..),
       Variable (..) )
import Kore.AST.Kore
       ( CommonKorePattern, asKorePattern )
import Kore.AST.MetaOrObject
import Kore.Building.AsAst
import Kore.Building.Sorts
import Kore.MetaML.Lift
       (liftToMeta)

{-| When defining new patterns (e.g. for new symbols and aliases),
users are expected to instantiate either
`ProperMetaPattern` or `ProperObjectPattern`, the other derivations
(e.g. for `MetaPattern` and `AsAst`) being inferred automatically.
-}
class MetaOrObject level => ProperPattern level sort patt | patt -> sort level where
    asProperPattern
        :: patt -> Pattern level Variable CommonKorePattern
type ProperMetaPattern = ProperPattern Meta
type ProperObjectPattern = ProperPattern Object

asProperObjectPattern :: (ProperPattern Object sort patt) =>
  patt -> Pattern Object Variable CommonKorePattern
asProperObjectPattern = asProperPattern
asProperMetaPattern :: (ProperPattern Meta sort patt) =>
  patt -> Pattern Meta Variable CommonKorePattern
asProperMetaPattern = asProperPattern

class AsAst CommonKorePattern patt => AsMetaPattern patt where
    asMetaPattern :: patt -> Pattern Meta Variable CommonKorePattern
class AsAst CommonKorePattern patt => AsObjectPattern patt where
    asObjectPattern :: patt -> Pattern Object Variable CommonKorePattern

class AsAst CommonKorePattern patt => ObjectPattern sort patt where
class AsAst CommonKorePattern patt => MetaPattern sort patt where

-------------------------------------

instance forall level sort patt . (ProperPattern level sort patt)
         => AsAst CommonKorePattern patt
  where
    asAst pat = case isMetaOrObject (Proxy :: Proxy level) of
      IsMeta   -> asKorePattern (asProperMetaPattern pat)
      IsObject -> asKorePattern (asProperObjectPattern pat)

instance ProperMetaPattern sort patt => MetaPattern sort patt where
instance ProperMetaPattern sort patt => AsMetaPattern patt where
    asMetaPattern = asProperMetaPattern

instance ProperObjectPattern sort patt => ObjectPattern sort patt where
instance ProperObjectPattern sort patt => AsObjectPattern patt where
    asObjectPattern = asProperObjectPattern

-------------------------------------

newtype ResultSort sort = ResultSort sort
newtype ContainedChild patt = ContainedChild patt

-------------------------------------

data PatternAnd pattern1 pattern2 sort level = PatternAnd
    { patternAndSort   :: sort
    , patternAndFirst  :: pattern1
    , patternAndSecond :: pattern2
    }
instance ( MetaOrObject level
         , AsSort level sort
         , ProperPattern level sort pattern1
         , ProperPattern level sort pattern2)
    => ProperPattern level sort (PatternAnd pattern1 pattern2 sort level)
  where
    asProperPattern (PatternAnd sort first second) =
        AndPattern (And (asAst sort) (asAst first) (asAst second))

type MetaAnd pattern1 pattern2 sort = PatternAnd pattern1 pattern2 sort Meta
metaAnd
    :: (MetaSort sort, MetaPattern sort pattern1, MetaPattern sort pattern2)
    => sort -> pattern1 -> pattern2 -> MetaAnd pattern1 pattern2 sort
metaAnd = PatternAnd

type ObjectAnd pattern1 pattern2 sort = PatternAnd pattern1 pattern2 sort Object
objectAnd
    ::  ( ObjectSort sort
        , ObjectPattern sort pattern1
        , ObjectPattern sort pattern2)
    => sort -> pattern1 -> pattern2 -> ObjectAnd pattern1 pattern2 sort
objectAnd = PatternAnd

-------------------------------------

newtype PatternBottom sort level = PatternBottom
    { patternBottomSort :: sort }
instance (MetaOrObject level, AsSort level sort) =>
          ProperPattern level sort (PatternBottom sort level)
  where
    asProperPattern (PatternBottom sort) =
        BottomPattern (Bottom (asAst sort))

type MetaBottom sort = PatternBottom sort Meta
metaBottom :: (MetaSort sort) => sort -> MetaBottom sort
metaBottom = PatternBottom

type ObjectBottom sort = PatternBottom sort Object
objectBottom :: ObjectSort sort => sort -> ObjectBottom sort
objectBottom = PatternBottom

-------------------------------------

data PatternCeil childSort child resultSort level = PatternCeil
    { patternCeilResultSort  :: ResultSort resultSort
    , patternCeilOperandSort :: childSort
    , patternCeilChild       :: child
    }
instance
    ( MetaOrObject level
    , AsSort level resultSort
    , AsSort level childSort
    , ProperPattern level childSort child)
    => ProperPattern level resultSort (PatternCeil childSort child resultSort level)
  where
    asProperPattern
        (PatternCeil (ResultSort resultSort) operandSort child)
      =
        CeilPattern Ceil
            { ceilOperandSort = asAst operandSort
            , ceilResultSort  = asAst resultSort
            , ceilChild       = asAst child
            }

type MetaCeil childSort child resultSort =
    PatternCeil childSort child resultSort Meta
metaCeil
    ::  ( MetaSort resultSort
        , MetaSort childSort
        , MetaPattern childSort child
        )
    => ResultSort resultSort
    -> childSort
    -> child
    -> MetaCeil childSort child resultSort
metaCeil = PatternCeil

type ObjectCeil childSort child resultSort =
    PatternCeil childSort child resultSort Object
objectCeil
    ::  ( ObjectSort resultSort
        , ObjectSort childSort
        , ObjectPattern childSort child
        )
    => ResultSort resultSort
    -> childSort
    -> child
    -> ObjectCeil childSort child resultSort
objectCeil = PatternCeil

-------------------------------------

data ObjectDomainValue pattern1 sort = ObjectDomainValue
    { patternDomainValueSort  :: sort
    , patternDomainValueChild :: pattern1
    }

instance
    ( ObjectSort sort
    , MetaPattern CharListSort pattern1
    ) => ProperPattern Object sort (ObjectDomainValue pattern1 sort)
  where
    asProperPattern (ObjectDomainValue sort child) =
        DomainValuePattern (DomainValue (asAst sort) (liftToMeta ast))
      where
        ast :: CommonKorePattern
        ast = asAst child
objectDomainValue
    :: (ObjectSort sort, MetaPattern CharListSort pattern1)
    => sort -> pattern1 -> ObjectDomainValue pattern1 sort
objectDomainValue = ObjectDomainValue

-------------------------------------

data PatternEquals childSort pattern1 pattern2 resultSort level = PatternEquals
    { patternEqualsResultSort  :: ResultSort resultSort
    , patternEqualsOperandSort :: childSort
    , patternEqualsFirst       :: pattern1
    , patternEqualsSecond      :: pattern2
    }
instance
    ( MetaOrObject level
    , AsSort level resultSort
    , AsSort level childSort
    , ProperPattern level childSort pattern1
    , ProperPattern level childSort pattern2)
    => ProperPattern level
        resultSort
        (PatternEquals childSort pattern1 pattern2 resultSort level)
  where
    asProperPattern
        (PatternEquals (ResultSort resultSort) operandSort first second)
      =
        EqualsPattern Equals
            { equalsOperandSort = asAst operandSort
            , equalsResultSort  = asAst resultSort
            , equalsFirst       = asAst first
            , equalsSecond      = asAst second
            }

type MetaEquals childSort pattern1 pattern2 resultSort =
    PatternEquals childSort pattern1 pattern2 resultSort Meta
metaEquals
    ::  ( MetaSort resultSort
        , MetaSort childSort
        , MetaPattern childSort pattern1
        , MetaPattern childSort pattern2
        )
    => ResultSort resultSort
    -> childSort
    -> pattern1
    -> pattern2
    -> MetaEquals childSort pattern1 pattern2 resultSort
metaEquals = PatternEquals

type ObjectEquals childSort pattern1 pattern2 resultSort =
    PatternEquals childSort pattern1 pattern2 resultSort Object
objectEquals
    ::  ( ObjectSort resultSort
        , ObjectSort childSort
        , ObjectPattern childSort pattern1
        , ObjectPattern childSort pattern2
        )
    => ResultSort resultSort
    -> childSort
    -> pattern1
    -> pattern2
    -> ObjectEquals childSort pattern1 pattern2 resultSort
objectEquals = PatternEquals

-------------------------------------

data PatternExists variable pattern1 sort level = PatternExists
    { metaExistsSort     :: sort
    , metaExistsVariable :: variable
    , metaExistsPattern  :: pattern1
    }

instance ( MetaOrObject level
         , AsSort level sort
         , AsSort level sv
         , ProperPattern level sort pattern1)
    => ProperPattern level sort (PatternExists (PatternVariable sv level) pattern1 sort level)
  where
    asProperPattern (PatternExists sort var patt) =
        ExistsPattern (Exists (asAst sort) (asVariable var) (asAst patt))

type MetaExists variable pattern1 sort =
    PatternExists variable pattern1 sort Meta
metaExists
    :: (MetaSort sort, MetaSort sv, MetaPattern sort pattern1)
    => sort
    -> MetaVariable sv
    -> pattern1
    -> MetaExists (MetaVariable sv) pattern1 sort
metaExists = PatternExists

type ObjectExists variable pattern1 sort =
    PatternExists variable pattern1 sort Object
objectExists
    :: (ObjectSort sort, ObjectSort sv, ObjectPattern sort pattern1)
    => sort
    -> ObjectVariable sv
    -> pattern1
    -> ObjectExists (ObjectVariable sv) pattern1 sort
objectExists = PatternExists

-------------------------------------

data PatternFloor childSort child resultSort level = PatternFloor
    { patternFloorResultSort  :: ResultSort resultSort
    , patternFloorOperandSort :: childSort
    , patternFloorChild       :: child
    }
instance
    ( MetaOrObject level
    , AsSort level resultSort
    , AsSort level childSort
    , ProperPattern level childSort child)
    => ProperPattern level resultSort (PatternFloor childSort child resultSort level)
  where
    asProperPattern
        (PatternFloor (ResultSort resultSort) operandSort child)
      =
        FloorPattern Floor
            { floorOperandSort = asAst operandSort
            , floorResultSort  = asAst resultSort
            , floorChild       = asAst child
            }

type MetaFloor childSort child resultSort =
    PatternFloor childSort child resultSort Meta
metaFloor
    ::  ( MetaSort resultSort
        , MetaSort childSort
        , MetaPattern childSort child
        )
    => ResultSort resultSort
    -> childSort
    -> child
    -> MetaFloor childSort child resultSort
metaFloor = PatternFloor

type ObjectFloor childSort child resultSort =
    PatternFloor childSort child resultSort Object
objectFloor
    ::  ( ObjectSort resultSort
        , ObjectSort childSort
        , ObjectPattern childSort child
        )
    => ResultSort resultSort
    -> childSort
    -> child
    -> ObjectFloor childSort child resultSort
objectFloor = PatternFloor

-------------------------------------

data PatternForall variable pattern1 sort level = PatternForall
    { patternForallSort     :: sort
    , patternForallVariable :: variable
    , patternForallPattern  :: pattern1
    }
instance ( MetaOrObject level
         , AsSort level sort
         , AsSort level variableSort
         , ProperPattern level sort pattern1)
    => ProperPattern level
        sort
        (PatternForall (PatternVariable variableSort level) pattern1 sort level)
  where
    asProperPattern (PatternForall sort var patt) =
        ForallPattern (Forall (asAst sort) (asVariable var) (asAst patt))

type MetaForall variable pattern1 sort =
    PatternForall variable pattern1 sort Meta
metaForall
    :: (MetaSort sort, MetaSort variableSort, MetaPattern sort pattern1)
    => sort
    -> MetaVariable variableSort
    -> pattern1
    -> MetaForall (MetaVariable variableSort) pattern1 sort
metaForall = PatternForall

type ObjectForall variable pattern1 sort =
    PatternForall variable pattern1 sort Object
objectForall
    :: (ObjectSort sort, ObjectSort variableSort, ObjectPattern sort pattern1)
    => sort
    -> ObjectVariable variableSort
    -> pattern1
    -> ObjectForall (ObjectVariable variableSort) pattern1 sort
objectForall = PatternForall

-------------------------------------

data PatternIff pattern1 pattern2 sort level = PatternIff
    { patternIffSort   :: sort
    , patternIffFirst  :: pattern1
    , patternIffSecond :: pattern2
    }
instance ( MetaOrObject level
         , AsSort level sort
         , ProperPattern level sort pattern1
         , ProperPattern level sort pattern2)
    => ProperPattern level sort (PatternIff pattern1 pattern2 sort level)
  where
    asProperPattern (PatternIff sort first second) =
        IffPattern (Iff (asAst sort) (asAst first) (asAst second))

type MetaIff pattern1 pattern2 sort = PatternIff pattern1 pattern2 sort Meta
metaIff
    :: (MetaSort sort, MetaPattern sort pattern1, MetaPattern sort pattern2)
    => sort -> pattern1 -> pattern2 -> MetaIff pattern1 pattern2 sort
metaIff = PatternIff

type ObjectIff pattern1 pattern2 sort = PatternIff pattern1 pattern2 sort Object
objectIff
    ::  ( ObjectSort sort
        , ObjectPattern sort pattern1
        , ObjectPattern sort pattern2
        )
    => sort -> pattern1 -> pattern2 -> ObjectIff pattern1 pattern2 sort
objectIff = PatternIff

-------------------------------------

data PatternImplies pattern1 pattern2 sort level = PatternImplies
    { patternImpliesSort   :: sort
    , patternImpliesFirst  :: pattern1
    , patternImpliesSecond :: pattern2
    }
instance ( MetaOrObject level
         , AsSort level sort
         , ProperPattern level sort pattern1
         , ProperPattern level sort pattern2)
    => ProperPattern level sort (PatternImplies pattern1 pattern2 sort level)
  where
    asProperPattern (PatternImplies sort first second) =
        ImpliesPattern (Implies (asAst sort) (asAst first) (asAst second))

type MetaImplies pattern1 pattern2 sort =
    PatternImplies pattern1 pattern2 sort Meta
metaImplies
    :: (MetaSort sort, MetaPattern sort pattern1, MetaPattern sort pattern2)
    => sort -> pattern1 -> pattern2 -> MetaImplies pattern1 pattern2 sort
metaImplies = PatternImplies

type ObjectImplies pattern1 pattern2 sort =
    PatternImplies pattern1 pattern2 sort Object
objectImplies
    ::  ( ObjectSort sort
        , ObjectPattern sort pattern1
        , ObjectPattern sort pattern2
        )
    => sort -> pattern1 -> pattern2 -> ObjectImplies pattern1 pattern2 sort
objectImplies = PatternImplies

-------------------------------------

data PatternIn childSort pattern1 pattern2 resultSort level = PatternIn
    { patternInResultSort      :: ResultSort resultSort
    , patternInOperandSort     :: childSort
    , patternInContainedChild  :: ContainedChild pattern1
    , patternInContainingChild :: pattern2
    }
instance
    ( MetaOrObject level
    , AsSort level resultSort
    , AsSort level childSort
    , ProperPattern level childSort pattern1
    , ProperPattern level childSort pattern2)
    => ProperPattern level resultSort (PatternIn childSort pattern1 pattern2 resultSort level)
  where
    asProperPattern
        (PatternIn
            (ResultSort resultSort) operandSort (ContainedChild first) second
        )
      =
        InPattern In
            { inOperandSort = asAst operandSort
            , inResultSort  = asAst resultSort
            , inContainedChild       = asAst first
            , inContainingChild      = asAst second
            }

type MetaIn childSort pattern1 pattern2 resultSort =
    PatternIn childSort pattern1 pattern2 resultSort Meta
metaIn
    ::  ( MetaSort resultSort
        , MetaSort childSort
        , MetaPattern childSort pattern1
        , MetaPattern childSort pattern2
        )
    => ResultSort resultSort
    -> childSort
    -> ContainedChild pattern1
    -> pattern2
    -> MetaIn childSort pattern1 pattern2 resultSort
metaIn = PatternIn

type ObjectIn childSort pattern1 pattern2 resultSort =
    PatternIn childSort pattern1 pattern2 resultSort Object
objectIn
    ::  ( ObjectSort resultSort
        , ObjectSort childSort
        , ObjectPattern childSort pattern1
        , ObjectPattern childSort pattern2
        )
    => ResultSort resultSort
    -> childSort
    -> ContainedChild pattern1
    -> pattern2
    -> ObjectIn childSort pattern1 pattern2 resultSort
objectIn = PatternIn

-------------------------------------

data ObjectNext pattern1 sort = ObjectNext
    { patternNextSort  :: sort
    , patternNextChild :: pattern1
    }

instance (ObjectSort sort, ObjectPattern sort pattern1)
    => ProperPattern Object sort (ObjectNext pattern1 sort)
  where
    asProperPattern (ObjectNext sort child) =
        NextPattern (Next (asAst sort) (asAst child))
objectNext
    :: (ObjectSort sort, ObjectPattern sort pattern1)
    => sort -> pattern1 -> ObjectNext pattern1 sort
objectNext = ObjectNext

-------------------------------------

data PatternNot pattern1 sort level = PatternNot
    { patternNotSort  :: sort
    , patternNotChild :: pattern1
    }
instance ( MetaOrObject level
         , AsSort level sort
         , ProperPattern level sort pattern1)
    => ProperPattern level sort (PatternNot pattern1 sort level)
  where
    asProperPattern (PatternNot sort child) =
        NotPattern (Not (asAst sort) (asAst child))

type MetaNot pattern1 sort = PatternNot pattern1 sort Meta
metaNot
    :: (MetaSort sort, MetaPattern sort pattern1)
    => sort -> pattern1 -> MetaNot pattern1 sort
metaNot = PatternNot

type ObjectNot pattern1 sort = PatternNot pattern1 sort Object
objectNot
    :: (ObjectSort sort, ObjectPattern sort pattern1)
    => sort -> pattern1 -> ObjectNot pattern1 sort
objectNot = PatternNot

-------------------------------------

data PatternOr pattern1 pattern2 sort level = PatternOr
    { patternOrSort   :: sort
    , patternOrFirst  :: pattern1
    , patternOrSecond :: pattern2
    }
instance ( MetaOrObject level
         , AsSort level sort
         , ProperPattern level sort pattern1
         , ProperPattern level sort pattern2)
    => ProperPattern level sort (PatternOr pattern1 pattern2 sort level)
  where
    asProperPattern (PatternOr sort pattern1 pattern2) =
        OrPattern (Or (asAst sort) (asAst pattern1) (asAst pattern2))

type MetaOr pattern1 pattern2 sort = PatternOr pattern1 pattern2 sort Meta
metaOr
    :: (MetaSort sort, MetaPattern sort pattern1, MetaPattern sort pattern2)
    => sort -> pattern1 -> pattern2 -> MetaOr pattern1 pattern2 sort
metaOr = PatternOr

type ObjectOr pattern1 pattern2 sort = PatternOr pattern1 pattern2 sort Object
objectOr
    ::  ( ObjectSort sort
        , ObjectPattern sort pattern1
        , ObjectPattern sort pattern2
        )
    => sort -> pattern1 -> pattern2 -> ObjectOr pattern1 pattern2 sort
objectOr = PatternOr

-------------------------------------

data ObjectRewrites pattern1 pattern2 sort = ObjectRewrites
    { patternRewritesSort   :: sort
    , patternRewritesFirst  :: pattern1
    , patternRewritesSecond :: pattern2
    }

instance
    ( ObjectSort sort
    , ObjectPattern sort pattern1
    , ObjectPattern sort pattern2
    )
    => ProperPattern Object sort (ObjectRewrites pattern1 pattern2 sort)
  where
    asProperPattern (ObjectRewrites sort pattern1 pattern2) =
        RewritesPattern
            (Rewrites (asAst sort) (asAst pattern1) (asAst pattern2))
objectRewrites
    ::  ( ObjectSort sort
        , ObjectPattern sort pattern1
        , ObjectPattern sort pattern2
        )
    => sort -> pattern1 -> pattern2 -> ObjectRewrites pattern1 pattern2 sort
objectRewrites = ObjectRewrites

-------------------------------------

newtype PatternTop sort level = PatternTop
    { patternTopSort :: sort }
instance (MetaOrObject level, AsSort level sort)
         => ProperPattern level sort (PatternTop sort level) where
    asProperPattern (PatternTop sort) =
        TopPattern (Top (asAst sort))

type MetaTop sort = PatternTop sort Meta
metaTop :: (MetaSort sort) => sort -> MetaTop sort
metaTop = PatternTop

type ObjectTop sort = PatternTop sort Object
objectTop :: ObjectSort sort => sort -> ObjectTop sort
objectTop = PatternTop

-------------------------------------

newtype MetaString = MetaString
    { patternStringValue :: String }

instance ProperPattern Meta CharListSort MetaString where
    asProperPattern (MetaString value) =
        StringLiteralPattern (StringLiteral value)
metaString :: String -> MetaString
metaString = MetaString

-------------------------------------

newtype MetaChar = MetaChar
    { patternCharValue :: Char }

instance ProperPattern Meta CharListSort MetaChar where
    asProperPattern (MetaChar value) =
        CharLiteralPattern (CharLiteral value)
metaChar :: Char -> MetaChar
metaChar = MetaChar

-------------------------------------

data PatternVariable sort level = PatternVariable
    { metaVariableName     :: !String
    , metaVariableLocation :: AstLocation
    , metaVariableSort     :: !sort
    }

instance ( MetaOrObject level
         , AsSort level sort)
  => ProperPattern level sort (PatternVariable sort level)
  where
    asProperPattern var =
        VariablePattern (asVariable var)
asVariable :: (MetaOrObject level, AsSort level sort)
           => PatternVariable sort level -> Variable level
asVariable (PatternVariable name location sort) =
    Variable (Id name location) (asAst sort)

type MetaVariable sort = PatternVariable sort Meta
metaVariable
    :: MetaSort sort
    => String -> AstLocation -> sort -> MetaVariable sort
metaVariable = PatternVariable
asMetaVariable :: MetaSort sort => MetaVariable sort -> Variable Meta
asMetaVariable (PatternVariable name location sort) =
    Variable (Id name location) (asAst sort)

type ObjectVariable sort = PatternVariable sort Object
objectVariable
    :: ObjectSort sort
    => String -> AstLocation -> sort -> ObjectVariable sort
objectVariable = PatternVariable
asObjectVariable :: ObjectSort sort => ObjectVariable sort -> Variable Object
asObjectVariable (PatternVariable name location sort) =
    Variable (Id name location) (asAst sort)
