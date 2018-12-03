{-|
Module      : Kore.MetaML.Builders
Description : Safe way to build larger 'level' patterns from components.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
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
    , parameterizedDomainValue_
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

import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.AST.BuildersImpl
import           Kore.AST.Pure
import           Kore.AST.Sentence
import           Kore.ASTHelpers
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Domain.Builtin as Domain
import           Kore.Error

{-|'sortParameter' defines a sort parameter that can be used in declarations.
-}
sortParameter :: Proxy level -> Text -> AstLocation -> SortVariable level
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
    ::  ( Functor domain
        , SentenceSymbolOrAlias s
        , Show level
        , Show (Pattern level domain Variable child)
        , child ~ PurePattern level domain Variable ()
        )
    => s level (PurePattern level) domain Variable
    -> [Sort level]
    -> [CommonPurePatternStub level domain ()]
    -> CommonPurePatternStub level domain ()
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
    ::  ( Functor domain
        , SentenceSymbolOrAlias s
        , Show level
        , Show (Pattern level domain Variable child)
        , child ~ PurePattern level domain Variable ()
        )
    => s level (PurePattern level) domain Variable
    -> [CommonPurePatternStub level domain ()]
    -> CommonPurePatternStub level domain ()
applyS sentence = applyPS sentence []

-- |Creates a 'level' 'Sort' from a given 'MetaSortType'
sort_ :: MetaSortType -> Sort level
sort_ sortType =
    SortActualSort SortActual
        { sortActualName = Id
            { getId = Text.pack (show sortType)
            , idLocation = AstLocationImplicit
            }
        , sortActualSorts = []
        }

-- |Given a string @name@, yields the 'UnsortedPatternStub' defining
-- name as a variable.
unparameterizedVariable_
    :: Text
    -> AstLocation
    -> CommonPurePatternStub level domain ()
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
    :: Sort level
    -> Text
    -> AstLocation
    -> CommonPurePatternStub level domain ()
parameterizedVariable_ sort name location =
    withSort sort (unparameterizedVariable_ name location)

-- |constructs an unparameterized Symbol declaration given the symbol name,
-- operand sorts and result sort.
symbol_
    :: Text
    -> AstLocation
    -> [Sort level]
    -> Sort level
    -> PureSentenceSymbol level domain
symbol_ name location = parameterizedSymbol_ name location []

-- |constructs a Symbol declaration given symbol name, parameters,
-- operand sorts and result sort.
parameterizedSymbol_
    :: Text
    -> AstLocation
    -> [SortVariable level]
    -> [Sort level]
    -> Sort level
    -> PureSentenceSymbol level domain
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
    :: Text
    -> AstLocation
    -> [Sort level]
    -> Sort level
    -> Pattern level domain Variable (CommonPurePattern level domain ())
    -> Pattern level domain Variable (CommonPurePattern level domain ())
    -> PureSentenceAlias level domain
alias_ name location = parameterizedAlias_ name location []

-- |constructs a Alias declaration given alias name, parameters,
-- operand sorts and result sort.
parameterizedAlias_
    :: Text
    -> AstLocation
    -> [SortVariable level]
    -> [Sort level]
    -> Sort level
    -> Pattern level domain Variable (CommonPurePattern level domain ())
    -> Pattern level domain Variable (CommonPurePattern level domain ())
    -> PureSentenceAlias level domain
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
bottom_ :: CommonPurePatternStub level domain ()
bottom_ = UnsortedPatternStub (BottomPattern . Bottom)

-- |A 'PatternStub' representing 'Top'.
top_ :: CommonPurePatternStub level domain ()
top_ = UnsortedPatternStub (TopPattern . Top)

-- |Builds a 'PatternStub' representing 'Equals' given the sort of the
-- operands and their corresponding 'PatternStub's.
equalsS_
    ::  ( Functor domain
        , MetaOrObject level
        , Show (CommonPurePattern level domain ())
        )
    => Sort level
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
equalsS_ s = equalsM_ (Just s)

-- |Builds a 'PatternStub' representing 'Equals' given the
-- corresponding 'PatternStub's.  Assumes operand sort is inferrable.
equals_
    ::  ( Functor domain
        , MetaOrObject level
        , Show (CommonPurePattern level domain ())
        )
    => CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
equals_ = equalsM_ Nothing

-- |Builds a 'PatternStub' representing 'In' given the sort of the
-- operands and their corresponding 'PatternStub's.
inS_
    ::  ( Functor domain
        , MetaOrObject level
        , Show (CommonPurePattern level domain ())
        )
    => Sort level
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
inS_ s = inM_ (Just s)

-- |Builds a 'PatternStub' representing 'In' given the
-- corresponding 'PatternStub's.  Assumes operand sort is inferrable.
in_
    ::  ( Functor domain
        , MetaOrObject level
        , Show (CommonPurePattern level domain ())
        )
    => CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
in_ = inM_ Nothing

-- |Builds a PatternStub representing 'Ceil' given the sort of the
-- operand and its corresponding 'PatternStub's.
ceilS_
    ::  ( Functor domain
        , MetaOrObject level
        , child ~ CommonPurePattern level domain ()
        , Show child
        , Show (Pattern level domain Variable child)
        )
    => Sort level
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
ceilS_ s = ceilM_ (Just s)

-- |Builds a 'PatternStub' representing 'Ceil' given the corresponding
-- operand 'PatternStub'.  Assumes operand sort is inferrable.
ceil_
    ::  ( Functor domain
        , MetaOrObject level
        , child ~ CommonPurePattern level domain ()
        , Show child
        , Show (Pattern level domain Variable child)
        )
    => CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
ceil_ = ceilM_ Nothing

-- |Builds a 'PatternStub' representing 'Floor' given the sort of the
-- operand and its corresponding 'PatternStub's.
floorS_
    ::  ( Functor domain
        , MetaOrObject level
        , child ~ CommonPurePattern level domain ()
        , Show child
        , Show (Pattern level domain Variable child)
        )
    => Sort level
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
floorS_ s = floorM_ (Just s)

-- |Builds a 'PatternStub' representing 'Floor' given the corresponding
-- operand 'PatternStub'.  Assumes operand sort is inferrable.
floor_
    ::  ( Functor domain
        , MetaOrObject level
        , child ~ CommonPurePattern level domain ()
        , Show child
        , Show (Pattern level domain Variable child)
        )
    => CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
floor_ = floorM_ Nothing

-- |Builds a 'PatternStub' representing 'Exists' given a variable and an
-- operand 'PatternStub'.
exists_
    :: (Functor domain, MetaOrObject level)
    => Variable level
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
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
    :: Functor domain
    => Variable level
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
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
    :: Functor domain
    => CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
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
    :: Functor domain
    => CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
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
    :: Functor domain
    => CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
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
    :: Functor domain
    => CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
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
not_
    :: Functor domain
    => CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
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
next_
    :: Functor domain
    => CommonPurePatternStub Object domain ()
    -> CommonPurePatternStub Object domain ()
next_ =
    unaryPattern
        (\sortS pattern1 ->
            NextPattern Next
                { nextSort   = sortS
                , nextChild  = pattern1
                }
        )

-- |Builds a 'PatternStub' representing 'DomainValue' given a 'Sort' and
-- a'String' for its operand.
parameterizedDomainValue_
    :: Sort Object -> String -> CommonPurePatternStub Object Domain.Builtin ()
parameterizedDomainValue_ sort str =
    SortedPatternStub
        SortedPattern
        { sortedPatternSort = sort
        , sortedPatternPattern =
            DomainValuePattern DomainValue
                { domainValueSort = sort
                , domainValueChild =
                    Domain.BuiltinPattern (StringLiteral_ str)
                }
        }

-- |Builds a 'PatternStub' representing 'Rewrites' given 'PatternStub's for its
-- operands.
rewrites_
    :: Functor domain
    => CommonPurePatternStub Object domain ()
    -> CommonPurePatternStub Object domain ()
    -> CommonPurePatternStub Object domain ()
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
    ::  ( Foldable domain
        , Functor domain
        , MetaOrObject level
        , child ~ CommonPurePattern level domain ()
        , Show child
        , Show (Pattern level domain Variable child)
        )
    => [SortVariable level]
    -> CommonPurePatternStub level domain ()
    -> PureSentenceAxiom level domain
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
        , sentenceAxiomPattern =
            quantifyFreeVariables s (asPurePattern $ () :< p)
        , sentenceAxiomAttributes = Attributes []
        }
{-|Creates an axiom with no sort parameters from a pattern.
-}
axiom_
    ::  ( Foldable domain
        , Functor domain
        , MetaOrObject level
        , child ~ CommonPurePattern level domain ()
        , Show child
        , Show (Pattern level domain Variable child)
        )
    => CommonPurePatternStub level domain ()
    -> PureSentenceAxiom level domain
axiom_ = parameterizedAxiom_ []

{-|'parameterizedEqualsAxiom_' is a special case for a 'parameterizedAxiom_' that
contains an equals pattern.
Since the result sort of equals is a parameter, this builder requires
passing as argument that `SortVariable`.
It is assumed that the sort variable is not used in any of
the patterns. Using it will have unpredictable effects.
-}
parameterizedEqualsAxiom_
    ::  ( Foldable domain
        , Functor domain
        , MetaOrObject level
        , child ~ CommonPurePattern level domain ()
        , Show child
        , Show (Pattern level domain Variable child)
        )
    => [SortVariable level]
    -> SortVariable level
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
    -> PureSentenceAxiom level domain
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
    ::  ( Foldable domain
        , Functor domain
        , MetaOrObject level
        , child ~ CommonPurePattern level domain ()
        , Show child
        , Show (Pattern level domain Variable child)
        )
    => SortVariable level
    -> CommonPurePatternStub level domain ()
    -> CommonPurePatternStub level domain ()
    -> PureSentenceAxiom level domain
equalsAxiom_ = parameterizedEqualsAxiom_ []
