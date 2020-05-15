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

import Data.Set
    ( Set
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Axiom.Concrete
    ( parseFreeVariables
    )
import Kore.Attribute.Parser as Parser
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , isFreeVariable
    , mapFreeVariables
    )
import Kore.Debug
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

instance From (Symbolic variable) (Set (UnifiedVariable variable)) where
    from = from @(FreeVariables _) . unSymbolic
    {-# INLINE from #-}

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
    parseApplication params args (Symbolic concreteVars) =
        Symbolic <$> parseFreeVariables freeVariables params args concreteVars

instance From (Symbolic Variable) Attributes where
    from =
        from @AttributePattern @Attributes
        . symbolicAttribute
        . FreeVariables.toList
        . unSymbolic

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
