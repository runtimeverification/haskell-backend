{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
 -}
module Kore.Attribute.Axiom.Symbolic
    ( Symbolic (..), isSymbolic
    , symbolicId, symbolicSymbol, symbolicAttribute
    , mapSymbolicVariables
    , parseSymbolicAttribute
    -- * Re-exports
    , FreeVariables
    ) where

import Prelude.Kore

import qualified Control.Monad as Monad
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , freeVariable
    , getFreeVariables
    , isFreeVariable
    , mapFreeVariables
    )
import Kore.Debug
import qualified Kore.Error
import Kore.Syntax.ElementVariable
import Kore.Syntax.SetVariable
import Kore.Syntax.Variable
    ( Variable
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )

{- | @Symbolic@ represents the @symbolic@ attribute for axioms.
 -}
newtype Symbolic variable =
    Symbolic { unSymbolic :: FreeVariables variable }
    deriving (Eq, GHC.Generic, Ord, Show, Semigroup, Monoid)

instance SOP.Generic (Symbolic variable)

instance SOP.HasDatatypeInfo (Symbolic variable)

instance Debug variable => Debug (Symbolic variable)

instance (Debug variable, Diff variable) => Diff (Symbolic variable)

instance NFData variable => NFData (Symbolic variable)

instance Ord variable => Default (Symbolic variable) where
    def = Symbolic mempty

-- | Kore identifier representing the @symbolic@ attribute symbol.
symbolicId :: Id
symbolicId = "symbolic"

-- | Kore symbol representing the @symbolic@ attribute.
symbolicSymbol :: SymbolOrAlias
symbolicSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = symbolicId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @symbolic@ attribute.
symbolicAttribute :: [UnifiedVariable Variable] -> AttributePattern
symbolicAttribute = attributePattern symbolicSymbol . map attributeVariable

parseSymbolicAttribute
    :: FreeVariables Variable
    -> AttributePattern
    -> Symbolic Variable
    -> Parser (Symbolic Variable)
parseSymbolicAttribute freeVariables =
    Parser.withApplication symbolicId parseApplication
  where
    parseApplication
        :: [Sort]
        -> [AttributePattern]
        -> Symbolic Variable
        -> Parser (Symbolic Variable)
    parseApplication params args (Symbolic symbolicVars) = do
        Parser.getZeroParams params
        vars <- mapM getVariable args
        mapM_ checkFree vars
        let newVars =
                if null vars then freeVariables else foldMap freeVariable vars
        mapM_ (checkDups symbolicVars) (getFreeVariables newVars)
        return (Symbolic $ symbolicVars <> newVars)
    checkFree :: UnifiedVariable Variable -> Parser ()
    checkFree variable =
        Monad.unless (isFreeVariable variable freeVariables)
        $ Kore.Error.koreFail
            ("expected free variable, found " ++ show variable)
    checkDups :: FreeVariables Variable -> UnifiedVariable Variable -> Parser ()
    checkDups freeVars var = Monad.when (isFreeVariable var freeVars)
        $ Kore.Error.koreFail
            ("duplicate symbolic variable declaration for " ++ show var)

instance From (Symbolic Variable) Attributes where
    from = from . symbolicAttribute . Set.toList . getFreeVariables . unSymbolic

mapSymbolicVariables
    :: Ord variable2
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable variable1 -> SetVariable variable2)
    ->  Symbolic variable1 -> Symbolic variable2
mapSymbolicVariables mapElemVar mapSetVar (Symbolic freeVariables) =
    Symbolic (mapFreeVariables mapElemVar mapSetVar freeVariables)

isSymbolic
    :: Ord variable => Symbolic variable -> UnifiedVariable variable -> Bool
isSymbolic (Symbolic vars) = not . flip isFreeVariable  vars
