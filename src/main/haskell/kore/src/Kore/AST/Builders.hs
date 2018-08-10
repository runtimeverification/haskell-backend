{-|
Module      : Kore.MetaML.Builders
Description : Safe way to build larger 'level' patterns from components.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.AST.Builders
    ( alias_
    , and_
    , axiom_
    , applyPS
    , applyS
    , bottom_ -- TODO: not used yet
    , ceilS_ -- TODO: not used yet
    , ceil_ -- TODO: not used yet
    , equalsAxiom_
    , equalsS_
    , equals_
    , exists_
    , floorS_ -- TODO: not used yet
    , floor_ -- TODO: not used yet
    , forall_
    , iff_ -- TODO: not used yet
    , implies_
    , inS_ -- TODO: not used yet
    , in_ -- TODO: not used yet
    , next_
    , not_
    , or_
    , parameterizedAxiom_
    , parameterizedEqualsAxiom_
    , parameterizedSymbol_
    , parameterizedVariable_
    , rewrites_
    , sortParameter
    , sort_
    , symbol_
    , top_
    , unparameterizedVariable_
    ) where

import Data.Functor.Foldable
       ( Fix (..) )
import Data.Proxy
       ( Proxy (..) )

import Kore.AST.BuildersImpl
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.AST.Sentence
import Kore.ASTHelpers
import Kore.Error

{-|'sortParameter' defines a sort parameter that can be used in declarations.
-}
sortParameter :: level -> String -> AstLocation -> SortVariable level
sortParameter _ name location =
    SortVariable Id
        { getId = name
        , idLocation = location
        }

{-|'applyPS' applies a symbol or alias declared by a given sentence to a list
of operands, using the provided sort arguments.

It can also be used to transform a symbol or alias sentence to something that
can be applied to patterns.
-}
applyPS
    :: (SentenceSymbolOrAlias s, Show level)
    => s level (Pattern level) Variable
    -> [Sort level]
    -> [CommonPurePatternStub level]
    -> CommonPurePatternStub level
applyPS sentence sortParameters patterns =
    SortedPatternStub SortedPattern
        { sortedPatternPattern =
            ApplicationPattern Application
                { applicationSymbolOrAlias =
                    getSentenceSymbolOrAliasHead sentence sortParameters
                , applicationChildren = fillCheckSorts argumentSorts patterns
                }
        , sortedPatternSort = returnSort
        }
  where
    applicationSorts =
        case symbolOrAliasSorts sortParameters sentence of
            Left err -> error (printError err)
            Right as -> as
    returnSort = applicationSortsResult applicationSorts
    argumentSorts = applicationSortsOperands applicationSorts

{-|'applyS' applies a symbol or alias without sort arguments, declared by a
given sentence, to a list of operands.

It can also be used to transform a symbol or alias sentence to something that
can be applied to patterns.
-}
applyS
    :: (SentenceSymbolOrAlias s, Show level)
    => s level (Pattern level) Variable
    -> [CommonPurePatternStub level]
    -> CommonPurePatternStub level
applyS sentence = applyPS sentence []

-- |Creates a 'level' 'Sort' from a given 'MetaSortType'
sort_ :: MetaSortType -> Sort level
sort_ sortType =
    SortActualSort SortActual
        { sortActualName = Id
            { getId = show sortType
            , idLocation = AstLocationImplicit
            }
        , sortActualSorts = []
        }

-- |Given a string @name@, yields the 'UnsortedPatternStub' defining
-- name as a variable.
unparameterizedVariable_ :: String -> AstLocation -> CommonPurePatternStub level
unparameterizedVariable_ name location =
    UnsortedPatternStub
        (\sortS ->
            VariablePattern Variable
                { variableName = Id
                    { getId = name
                    , idLocation = location
                    }
                , variableSort = sortS
                }
        )

-- |Given a 'Sort' @sort@ and a string @name@, yields 'PatternStub' defining
-- name as a variable of sort @sort@.
parameterizedVariable_
    :: Sort level -> String -> AstLocation -> CommonPurePatternStub level
parameterizedVariable_ sort name location =
    withSort sort (unparameterizedVariable_ name location)

-- |constructs an unparameterized Symbol declaration given the symbol name,
-- operand sorts and result sort.
symbol_
    :: String
    -> AstLocation
    -> [Sort level]
    -> Sort level
    -> PureSentenceSymbol level
symbol_ name location = parameterizedSymbol_ name location []

-- |constructs a Symbol declaration given symbol name, parameters,
-- operand sorts and result sort.
parameterizedSymbol_
    :: String
    -> AstLocation
    -> [SortVariable level]
    -> [Sort level]
    -> Sort level
    -> PureSentenceSymbol level
parameterizedSymbol_ name location parameters operandSorts resultSort =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id
                { getId = name
                , idLocation = location
                }
            , symbolParams = parameters
            }
        , sentenceSymbolSorts = operandSorts
        , sentenceSymbolResultSort = resultSort
        , sentenceSymbolAttributes = Attributes []
        }

-- |constructs an unparameterized Alias declaration given the alias name,
-- operand sorts and result sort.
alias_
    :: String
    -> AstLocation
    -> [Sort level]
    -> Sort level
    -> Pattern level Variable (Fix (Pattern level Variable))
    -> Pattern level Variable (Fix (Pattern level Variable))
    -> PureSentenceAlias level
alias_ name location = parameterizedAlias_ name location []

-- |constructs a Alias declaration given alias name, parameters,
-- operand sorts and result sort.
parameterizedAlias_
    :: String
    -> AstLocation
    -> [SortVariable level]
    -> [Sort level]
    -> Sort level
    -> Pattern level Variable (Fix (Pattern level Variable))
    -> Pattern level Variable (Fix (Pattern level Variable))
    -> PureSentenceAlias level
parameterizedAlias_ name location parameters operandSorts resultSort leftPat rightPat =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id
                { getId = name
                , idLocation = location
                }
            , aliasParams = parameters
            }
        , sentenceAliasSorts = operandSorts
        , sentenceAliasResultSort = resultSort
        , sentenceAliasLeftPattern = leftPat
        , sentenceAliasRightPattern = rightPat
        , sentenceAliasAttributes = Attributes []
        }

-- |A 'PatternStub' representing 'Bottom'.
bottom_ :: CommonPurePatternStub level
bottom_ = UnsortedPatternStub (BottomPattern . Bottom)

-- |A 'PatternStub' representing 'Top'.
top_ :: CommonPurePatternStub level
top_ = UnsortedPatternStub (TopPattern . Top)

-- |Builds a 'PatternStub' representing 'Equals' given the sort of the
-- operands and their corresponding 'PatternStub's.
equalsS_
    :: (MetaOrObject level)
    => Sort level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
equalsS_ s = equalsM_ (Just s)

-- |Builds a 'PatternStub' representing 'Equals' given the
-- corresponding 'PatternStub's.  Assumes operand sort is inferrable.
equals_
    :: (MetaOrObject level)
    => CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
equals_ = equalsM_ Nothing

-- |Builds a 'PatternStub' representing 'In' given the sort of the
-- operands and their corresponding 'PatternStub's.
inS_
    :: (MetaOrObject level)
    => Sort level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
inS_ s = inM_ (Just s)

-- |Builds a 'PatternStub' representing 'In' given the
-- corresponding 'PatternStub's.  Assumes operand sort is inferrable.
in_
    :: (MetaOrObject level)
    => CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
in_ = inM_ Nothing

-- |Builds a PatternStub representing 'Ceil' given the sort of the
-- operand and its corresponding 'PatternStub's.
ceilS_
    :: (MetaOrObject level)
    => Sort level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
ceilS_ s = ceilM_ (Just s)

-- |Builds a 'PatternStub' representing 'Ceil' given the corresponding
-- operand 'PatternStub'.  Assumes operand sort is inferrable.
ceil_
    :: (MetaOrObject level)
    => CommonPurePatternStub level -> CommonPurePatternStub level
ceil_ = ceilM_ Nothing

-- |Builds a 'PatternStub' representing 'Floor' given the sort of the
-- operand and its corresponding 'PatternStub's.
floorS_
    :: (MetaOrObject level)
    => Sort level -> CommonPurePatternStub level -> CommonPurePatternStub level
floorS_ s = floorM_ (Just s)

-- |Builds a 'PatternStub' representing 'Floor' given the corresponding
-- operand 'PatternStub'.  Assumes operand sort is inferrable.
floor_
    :: (MetaOrObject level)
    => CommonPurePatternStub level -> CommonPurePatternStub level
floor_ = floorM_ Nothing

-- |Builds a 'PatternStub' representing 'Exists' given a variable and an
-- operand 'PatternStub'.
exists_
    :: (MetaOrObject level)
    => Variable level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
exists_ variable1 =
    unaryPattern
        (\sortS pattern1 ->
            ExistsPattern Exists
                { existsSort     = sortS
                , existsVariable = variable1
                , existsChild    = pattern1
                }
        )

-- |Builds a 'PatternStub' representing 'Forall' given a variable and an
-- operand 'PatternStub'.
forall_
    :: Variable level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
forall_ variable1 =
    unaryPattern
        (\sortS pattern1 ->
            ForallPattern Forall
                { forallSort     = sortS
                , forallVariable = variable1
                , forallChild    = pattern1
                }
        )

-- |Builds a 'PatternStub' representing 'Or' given 'PatternStub's for its
-- operands.
or_
    :: CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
or_ =
    binaryPattern
        (\commonSort firstPattern secondPattern ->
            OrPattern Or
                { orSort   = commonSort
                , orFirst  = firstPattern
                , orSecond = secondPattern
                }
        )

-- |Builds a 'PatternStub' representing 'And' given 'PatternStub's for its
-- operands.
and_
    :: CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
and_ =
    binaryPattern
        (\commonSort firstPattern secondPattern ->
            AndPattern And
                { andSort   = commonSort
                , andFirst  = firstPattern
                , andSecond = secondPattern
                }
        )

-- |Builds a 'PatternStub' representing 'Iff' given 'PatternStub's for its
-- operands.
iff_
    :: CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
iff_ =
    binaryPattern
        (\commonSort firstPattern secondPattern ->
            IffPattern Iff
                { iffSort   = commonSort
                , iffFirst  = firstPattern
                , iffSecond = secondPattern
                }
        )

-- |Builds a 'PatternStub' representing 'Implies' given 'PatternStub's for
-- its operands.
implies_
    :: CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
implies_ =
    binaryPattern
        (\commonSort firstPattern secondPattern ->
            ImpliesPattern Implies
                { impliesSort   = commonSort
                , impliesFirst  = firstPattern
                , impliesSecond = secondPattern
                }
        )

-- |Builds a 'PatternStub' representing 'Not' given a 'PatternStub' for
-- its operand.
not_ :: CommonPurePatternStub level -> CommonPurePatternStub level
not_ =
    unaryPattern
        (\sortS pattern1 ->
            NotPattern Not
                { notSort   = sortS
                , notChild  = pattern1
                }
        )

-- |Builds a 'PatternStub' representing 'Next' given a 'PatternStub' for
-- its operand.
next_ :: CommonPurePatternStub Object -> CommonPurePatternStub Object
next_ =
    unaryPattern
        (\sortS pattern1 ->
            NextPattern Next
                { nextSort   = sortS
                , nextChild  = pattern1
                }
        )

-- |Builds a 'PatternStub' representing 'Rewrites' given 'PatternStub's for its
-- operands.
rewrites_
    :: CommonPurePatternStub Object
    -> CommonPurePatternStub Object
    -> CommonPurePatternStub Object
rewrites_ =
    binaryPattern
        (\commonSort firstPattern secondPattern ->
            RewritesPattern Rewrites
                { rewritesSort   = commonSort
                , rewritesFirst  = firstPattern
                , rewritesSecond = secondPattern
                }
        )

{-|'parameterizedAxiom_' creates an axiom that has sort parameters from
a pattern.
-}
parameterizedAxiom_
    :: MetaOrObject level
    => [SortVariable level]
    -> CommonPurePatternStub level
    -> PureSentenceAxiom level
parameterizedAxiom_ _ (UnsortedPatternStub p) =
    error
        (  "Cannot infer sort for "
        ++ show (p (dummySort (Proxy :: Proxy level))) ++ "."
        )
parameterizedAxiom_
    parameters
    ( SortedPatternStub SortedPattern
        { sortedPatternPattern = p, sortedPatternSort = s }
    )
  =
    SentenceAxiom
        { sentenceAxiomParameters = parameters
        , sentenceAxiomPattern = quantifyFreeVariables s (Fix p)
        , sentenceAxiomAttributes = Attributes []
        }
{-|Creates an axiom with no sort parameters from a pattern.
-}
axiom_
    :: MetaOrObject level
    => CommonPurePatternStub level
    -> PureSentenceAxiom level
axiom_ = parameterizedAxiom_ []

{-|'parameterizedEqualsAxiom_' is a special case for a 'parameterizedAxiom_' that
contains an equals pattern.
Since the result sort of equals is a parameter, this builder requires
passing as argument that `SortVariable`.
It is assumed that the sort variable is not used in any of
the patterns. Using it will have unpredictable effects.
-}
parameterizedEqualsAxiom_
    :: MetaOrObject level
    => [SortVariable level]
    -> SortVariable level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> PureSentenceAxiom level
parameterizedEqualsAxiom_ parameters equalsSortParam first second =
    parameterizedAxiom_
        (equalsSortParam : parameters)
        (withSort (SortVariableSort equalsSortParam) (equals_ first second))

{-|'equalsAxiom_' is a special case for an axiom that contains an equals pattern.
Since the result sort of equals is a parameter, this builder requires
passing as argument that `SortVariable`.
It is assumed that the sort variable is not used in any of
the patterns. Using it will have unpredictable effects.
-}
equalsAxiom_
    :: MetaOrObject level
    => SortVariable level
    -> CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> PureSentenceAxiom level
equalsAxiom_ = parameterizedEqualsAxiom_ []
