module Test.Kore.Builtin.AssocComm.CeilSimplifier
    ( hprop_Builtin_Map
    , hprop_Builtin_Set
    ) where

import Prelude.Kore

import Hedgehog hiding
    ( test
    )
import qualified Hedgehog.Gen as Gen

import Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makeCeilPredicate_
    , makeEqualsPredicate_
    , makeNotPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import qualified Kore.Step.Simplification.Ceil as Ceil
    ( makeEvaluate
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification

hprop_Builtin_Map :: Property
hprop_Builtin_Set :: Property
(hprop_Builtin_Map, hprop_Builtin_Set) =
    ( propertyBuiltinAssocComm
        (genKeys >>= traverse genMapElement)
        (Gen.subsequence opaqueMaps)
        fst
        defineMapElement
        Mock.framedMap
    , propertyBuiltinAssocComm
        genKeys
        (Gen.subsequence opaqueSets)
        id
        defineSetElement
        Mock.framedSet
    )
  where
    nullaryCtors = [Mock.a, Mock.b, Mock.c]
    elemVars = [Mock.x, Mock.y, Mock.z]
    opaqueMaps = Mock.opaqueMap . mkElemVar <$> elemVars
    opaqueSets = Mock.opaqueSet . mkElemVar <$> elemVars
    genKeys = Gen.subsequence keys
    keys =
        -- concrete keys
        nullaryCtors
        -- symbolic keys
        ++ (Mock.f . mkElemVar <$> elemVars)
    genMapElement key = (,) key <$> genVal
    genVal = Gen.element vals
    vals =
        -- concrete values
        (Mock.constr10 <$> nullaryCtors)
        -- symbolic values
        ++ (Mock.g . mkElemVar <$> elemVars)

    defineMapElement (key, val) =
        -- symbolic keys are defined
        [ makeCeilPredicate_ key | (not . isConcrete) key ]
        ++
        -- symbolic values are defined
        [ makeCeilPredicate_ val | (not . isConcrete) val ]

    defineSetElement key =
        -- symbolic keys are defined
        [ makeCeilPredicate_ key | (not . isConcrete) key ]

propertyBuiltinAssocComm
    :: Show element
    => Gen [element]
    -> Gen [TermLike Variable]
    -> (element -> TermLike Variable)
    -> (element -> [Predicate Variable])
    -> ([element] -> [TermLike Variable] -> TermLike Variable)
    -> Property
propertyBuiltinAssocComm
    genElements
    genOpaques
    elementKey
    defineElement
    mkAssocComm
  = Hedgehog.property $ do
    opaques <- forAll genOpaques
    elements <- forAll genElements
    let original = Pattern.fromTermLike $ mkAssocComm elements opaques
        keys = elementKey <$> elements
    actualPattern <-
        (liftIO . makeEvaluate) original
        >>= (return . OrPattern.toPatterns)
        >>= \case { [actualPattern] -> return actualPattern; _ -> failure }
    Hedgehog.assert (isTop $ term actualPattern)
    Hedgehog.assert (Substitution.null $ substitution actualPattern)
    let actualPredicates =
            predicate actualPattern
            & Predicate.getMultiAndPredicate
            & MultiAnd.make
        -- | Elements are defined
        expectDefinedElements = elements >>= defineElement
        -- | Opaque operands are defined
        expectDefinedOpaques = makeCeilPredicate_ <$> opaques
        -- | Keys are distinct
        expectDistinctKeys =
            [ uncurry makeNotEqualsPredicate $ minMax key1 key2
            | (key1, key2) <- zipWithTails (,) keys
            -- concrete keys are assumed to be distinct among the
            -- concrete keys, but not among the symbolic keys
            , not (isConcrete key1 && isConcrete key2)
            ]
        -- | No element occurs in any opaque operand
        expectNoElementInOpaque =
            [ makeCeilPredicate_ $ mkAssocComm [element] [opaque']
            | element <- elements
            , opaque' <- opaques
            ]
        -- | Opaque operands are distinct
        expectDistinctOpaques =
            [ makeCeilPredicate_ $ mkAssocComm [] [opaque1, opaque2]
            | (opaque1, opaque2) <- zipWithTails (,) opaques
            ]
        expectPredicates =
            (MultiAnd.make . concat)
                [ expectDefinedElements
                , expectDefinedOpaques
                , expectDistinctKeys
                , expectNoElementInOpaque
                , expectDistinctOpaques
                ]
    expectPredicates === actualPredicates
  where
    makeNotEqualsPredicate x y = makeNotPredicate $ makeEqualsPredicate_ x y

    zipWithTails :: (a -> a -> b) -> [a] -> [b]
    zipWithTails _ [] = []
    zipWithTails f (x : xs) = map (f x) xs ++ zipWithTails f xs

makeEvaluate :: Pattern Variable -> IO (OrPattern Variable)
makeEvaluate child =
    runSimplifierNoSMT mockEnv
    $ Ceil.makeEvaluate SideCondition.top child
  where
    mockEnv = Mock.env { simplifierAxioms = mempty }
