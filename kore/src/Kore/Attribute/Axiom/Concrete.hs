{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Attribute.Axiom.Concrete
    ( Concrete (..), isConcrete
    , concreteId, concreteSymbol, concreteAttribute
    , mapConcreteVariables
    , parseConcreteAttribute
    , parseFreeVariables -- used by Symbolic
    -- * Re-exports
    , FreeVariables
    ) where

import Prelude.Kore

import qualified Control.Error as Safe
import qualified Control.Monad as Monad
import qualified Data.List as List
import Data.Set
    ( Set
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , freeVariable
    , isFreeVariable
    , mapFreeVariables
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Debug
import qualified Kore.Error
import Kore.Syntax.Variable hiding
    ( Concrete
    )
import Kore.Variables.UnifiedVariable

{- | @Concrete@ represents the @concrete@ attribute for axioms.
 -}
newtype Concrete variable =
    Concrete { unConcrete :: FreeVariables variable }
    deriving (Eq, GHC.Generic, Ord, Show, Semigroup, Monoid)

instance SOP.Generic (Concrete variable)

instance SOP.HasDatatypeInfo (Concrete variable)

instance Debug variable => Debug (Concrete variable)

instance (Debug variable, Diff variable) => Diff (Concrete variable)

instance NFData variable => NFData (Concrete variable)

instance Ord variable => Default (Concrete variable) where
    def = Concrete mempty

instance From (Concrete variable) (Set (UnifiedVariable variable)) where
    from = from @(FreeVariables _) . unConcrete
    {-# INLINE from #-}

-- | Kore identifier representing the @concrete@ attribute symbol.
concreteId :: Id
concreteId = "concrete"

-- | Kore symbol representing the @concrete@ attribute.
concreteSymbol :: SymbolOrAlias
concreteSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = concreteId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @concrete@ attribute.
concreteAttribute :: [UnifiedVariable Variable] -> AttributePattern
concreteAttribute = attributePattern concreteSymbol . map attributeVariable

parseConcreteAttribute
    :: FreeVariables Variable
    -> AttributePattern
    -> Concrete Variable
    -> Parser (Concrete Variable)
parseConcreteAttribute freeVariables =
    Parser.withApplication concreteId parseApplication
  where
    parseApplication params args (Concrete concreteVars) =
        Concrete <$> parseFreeVariables freeVariables params args concreteVars

parseFreeVariables
    :: FreeVariables Variable
    -> [Sort]
    -> [AttributePattern]
    -> FreeVariables Variable
    -> Parser (FreeVariables Variable)
parseFreeVariables freeVariables params args concreteVars = do
    Parser.getZeroParams params
    vars <- mapM getVariable args
    mapM_ checkFree vars
    let newVars = -- if no arguments are provides, assume all free variables
            if null vars
                then FreeVariables.toList freeVariables
                else vars
        allVars = newVars ++ FreeVariables.toList concreteVars
        groupedVars = List.group . List.sort $ allVars
        nubVars = mapMaybe Safe.headMay groupedVars
        duplicateVars =
            mapMaybe (Safe.headMay Monad.<=< Safe.tailMay) groupedVars
    unless (null duplicateVars)
        $ Kore.Error.koreFail
            ("duplicate concrete/symbolic variable annotations for "
            ++ show duplicateVars)
    return (foldMap freeVariable nubVars)
  where
    checkFree :: UnifiedVariable Variable -> Parser ()
    checkFree variable =
        unless (isFreeVariable variable freeVariables)
        $ Kore.Error.koreFail
            ("expected free variable, found " ++ show variable)

instance From (Concrete Variable) Attributes where
    from =
        from @AttributePattern
        . concreteAttribute
        . FreeVariables.toList
        . unConcrete

mapConcreteVariables
    ::  (NamedVariable variable1, NamedVariable variable2)
    =>  AdjSomeVariableName
            (VariableNameOf variable1 -> VariableNameOf variable2)
    ->  Concrete variable1
    ->  Concrete variable2
mapConcreteVariables adj (Concrete freeVariables) =
    Concrete (mapFreeVariables adj freeVariables)

isConcrete
    :: Ord variable => Concrete variable -> UnifiedVariable variable -> Bool
isConcrete Concrete { unConcrete } var = isFreeVariable var unConcrete
