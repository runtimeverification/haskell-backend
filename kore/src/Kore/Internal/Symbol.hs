{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Internal.Symbol
    ( Symbol (..)
    , toSymbolOrAlias
    , isNonSimplifiable
    , isConstructor
    , isSortInjection
    , isFunctional
    , isFunction
    , isTotal
    , isInjective
    , isMemo
    , symbolHook
    , constructor
    , functional
    , function
    , injective
    , sortInjection
    , smthook
    , hook
    , coerceSortInjection
    -- * Re-exports
    , module Kore.Internal.ApplicationSorts
    ) where

import Control.DeepSeq
import qualified Control.Lens as Lens hiding
    ( makeLenses
    )
import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import Data.Generics.Product
import Data.Hashable
import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
import qualified Kore.Attribute.Symbol as Attribute
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Internal.ApplicationSorts
import Kore.Sort
import Kore.Syntax.Application
import Kore.Unparser
import SMT.AST
    ( SExpr
    )

data Symbol =
    Symbol
        { symbolConstructor :: !Id
        , symbolParams      :: ![Sort]
        , symbolSorts       :: !ApplicationSorts
        , symbolAttributes  :: !Attribute.Symbol
        }
    deriving (GHC.Generic, Show)

instance Eq Symbol where
    (==) a b =
            Function.on (==) symbolConstructor a b
        &&  Function.on (==) symbolParams a b
    {-# INLINE (==) #-}

instance Ord Symbol where
    compare a b =
            Function.on compare symbolConstructor a b
        <>  Function.on compare symbolParams a b

instance Hashable Symbol where
    hashWithSalt salt Symbol { symbolConstructor, symbolParams } =
        salt `hashWithSalt` symbolConstructor `hashWithSalt` symbolParams

instance NFData Symbol

instance SOP.Generic Symbol

instance SOP.HasDatatypeInfo Symbol

instance Debug Symbol

instance Diff Symbol

instance Unparse Symbol where
    unparse Symbol { symbolConstructor, symbolParams } =
        unparse symbolConstructor <> parameters symbolParams

    unparse2 Symbol { symbolConstructor } =
        unparse2 symbolConstructor

instance
    Ord variable
    => Synthetic (FreeVariables variable) (Application Symbol)
  where
    synthetic = Foldable.fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (Application Symbol) where
    synthetic application =
        resultSort Function.& deepseq (matchSorts operandSorts children)
      where
        Application { applicationSymbolOrAlias = symbol } = application
        Application { applicationChildren = children } = application
        Symbol { symbolSorts } = symbol
        resultSort = applicationSortsResult symbolSorts
        operandSorts = applicationSortsOperands symbolSorts

toSymbolOrAlias :: Symbol -> SymbolOrAlias
toSymbolOrAlias symbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = symbolConstructor symbol
        , symbolOrAliasParams = symbolParams symbol
        }

-- | Is a symbol not simplifiable?
--
-- sigma is non-simplifiable if whenever we have the following
-- * Context[y] is not simplifiable to a pattern without y
-- * sigma(..., x, ...) != bottom
-- then Context[sigma(..., x, ...)] cannot be simplified to either x or
-- something that does not contain x as a free variable.
--
-- Note that constructors and sort injection are natural candidates for
-- non-simplifiable patterns. Builtins like 'element' (for sets, lists and maps)
-- are also good candidates for non-simplifiable symbols.
--
-- Builtins like 'concat' need an additional condition, i.e. that the arguments
-- are not .Map.
isNonSimplifiable :: Symbol -> Bool
isNonSimplifiable = Attribute.isNonSimplifiable . symbolAttributes

isConstructor :: Symbol -> Bool
isConstructor =
    Attribute.isConstructor . Attribute.constructor . symbolAttributes

isSortInjection :: Symbol -> Bool
isSortInjection =
    Attribute.isSortInjection . Attribute.sortInjection . symbolAttributes

isInjective :: Symbol -> Bool
isInjective = Attribute.isInjective . symbolAttributes

isFunctional :: Symbol -> Bool
isFunctional = Attribute.isFunctional . symbolAttributes

isFunction :: Symbol -> Bool
isFunction = Attribute.isFunction . symbolAttributes

isTotal :: Symbol -> Bool
isTotal = Attribute.isTotal . symbolAttributes

isMemo :: Symbol -> Bool
isMemo = Attribute.isMemo . Attribute.memo . symbolAttributes

symbolHook :: Symbol -> Attribute.Hook
symbolHook = Attribute.hook . symbolAttributes

constructor :: Symbol -> Symbol
constructor =
    Lens.set
        (typed @Attribute.Symbol . typed @Attribute.Constructor)
        Attribute.Constructor { isConstructor = True }

functional :: Symbol -> Symbol
functional =
    Lens.set
        (typed @Attribute.Symbol . typed @Attribute.Functional)
        Attribute.Functional { isDeclaredFunctional = True }

function :: Symbol -> Symbol
function =
    Lens.set
        (typed @Attribute.Symbol . typed @Attribute.Function)
        Attribute.Function { isDeclaredFunction = True }

injective :: Symbol -> Symbol
injective =
    Lens.set
        (typed @Attribute.Symbol . typed @Attribute.Injective)
        Attribute.Injective { isDeclaredInjective = True }

sortInjection :: Symbol -> Symbol
sortInjection =
    Lens.set
        (typed @Attribute.Symbol . typed @Attribute.SortInjection)
        Attribute.SortInjection { isSortInjection = True }

smthook :: SExpr -> Symbol -> Symbol
smthook sExpr =
    Lens.set
        (typed @Attribute.Symbol . typed @Attribute.Smthook)
        Attribute.Smthook { getSmthook = Just sExpr }

hook :: Text -> Symbol -> Symbol
hook name =
    Lens.set
        (typed @Attribute.Symbol . typed @Attribute.Hook)
        Attribute.Hook { getHook = Just name }

{- | Coerce a sort injection symbol's source and target sorts.

Use @coerceSortInjection@ to update the internal representation of a sort
injection 'Symbol' when evaluating or simplifying sort injections.

 -}
coerceSortInjection
    :: Symbol
    -- ^ Original sort injection symbol
    -> Sort
    -- ^ New source sort
    -> Sort
    -- ^ New target sort
    -> Symbol
coerceSortInjection injectionSymbol sourceSort targetSort =
    injectionSymbol
        { symbolParams = [sourceSort, targetSort]
        , symbolSorts = applicationSorts [sourceSort] targetSort
        }
