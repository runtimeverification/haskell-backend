{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module Kore.LLVM.TH (dynamicBindings) where

import Control.Monad.Trans.Reader (ReaderT (..))
import Data.List (isPrefixOf)
import Data.Map qualified as Map
import Foreign (FunPtr, Ptr)
import Foreign.C.Types qualified as Foreign.C
import Language.C qualified as C
import Language.C.Analysis.AstAnalysis qualified as C
import Language.C.Analysis.SemRep qualified as C
import Language.C.Analysis.TravMonad qualified as C
import Language.C.Data.Ident qualified as C
import Language.C.System.GCC qualified as C
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Syntax qualified as TH
import System.Posix.DynamicLinker qualified as Linker
import Text.Casing (Identifier (..), fromAny, toCamel, toPascal)

dynamicBindings :: FilePath -> TH.Q [TH.Dec]
dynamicBindings headerFile =
    TH.qAddDependentFile headerFile
        >> (TH.runIO $ parseCHeader headerFile)
        >>= addDefinitions
  where
    addDefinitions = \case
        [] -> pure []
        (C.Ident nm _ _, C.Declaration (C.Decl (C.VarDecl _ _ ty) _)) : xs ->
            if "__" `isPrefixOf` nm
                then addDefinitions xs
                else do
                    defs <- foreignImport nm ty
                    (defs ++) <$> addDefinitions xs
        _ : xs -> addDefinitions xs

parseCHeader :: FilePath -> IO [(C.Ident, C.IdentDecl)]
parseCHeader input_file =
    do
        parse_result <- C.parseCFile (C.newGCC "gcc") Nothing [] input_file
        case parse_result of
            Left parse_err -> error (show parse_err)
            Right ast -> case C.runTrav_ $ C.gObjs <$> C.analyseAST ast of
                Left err -> error (show err)
                Right (m, _) -> pure $ Map.toList m

foreignImport :: String -> C.Type -> TH.Q [TH.Dec]
foreignImport name' ty' = do
    ty <- cTypeToHs ty'
    let nameUnwrap = TH.mkName $ toCamel $ (Identifier . (++ ["unwrap"]) . unIdentifier) $ fromAny name'
        nameFunPtr = TH.mkName $ toCamel $ (Identifier . (++ ["fun", "ptr"]) . unIdentifier) $ fromAny name'
        name = TH.mkName $ toCamel $ fromAny name'
    libHandle <- TH.newName "libHandle"

    pure
        [ -- foreign import ccall "dynamic" <camel_name>Unwrap :: FunPtr <ty> -> <ty>
          TH.ForeignD $ TH.ImportF TH.CCall TH.Safe "dynamic" nameUnwrap $ TH.AppT (TH.AppT TH.ArrowT $ TH.AppT (TH.ConT ''FunPtr) ty) ty
        , -- <camel_name>FunPtr :: ReaderT DL IO (FunPtr <ty>)
          TH.SigD
            nameFunPtr
            (TH.AppT (TH.AppT (TH.AppT (TH.ConT ''ReaderT) (TH.ConT ''Linker.DL)) (TH.ConT ''IO)) (TH.AppT (TH.ConT ''FunPtr) ty))
        , -- <camel_name>FunPtr = ReaderT $ \libHandle -> Linker.dlsym libHandle "<name>"
          TH.ValD
            (TH.VarP nameFunPtr)
            ( TH.NormalB
                ( TH.InfixE
                    (Just (TH.ConE 'ReaderT))
                    (TH.VarE '($))
                    (Just $ TH.LamE [TH.VarP libHandle] $ TH.AppE (TH.AppE (TH.VarE 'Linker.dlsym) $ TH.VarE libHandle) (TH.LitE $ TH.StringL name'))
                )
            )
            []
        , -- <camel_name> :: ReaderT DL IO <ty>
          TH.SigD
            name
            (TH.AppT (TH.AppT (TH.AppT (TH.ConT ''ReaderT) (TH.ConT ''Linker.DL)) (TH.ConT ''IO)) ty)
        , -- <camel_name> = <camel_name>Unwrap <$> <camel_name>FunPtr
          TH.ValD
            (TH.VarP name)
            ( TH.NormalB
                ( TH.InfixE
                    (Just (TH.VarE nameUnwrap))
                    (TH.VarE '(<$>))
                    (Just (TH.VarE nameFunPtr))
                )
            )
            []
        ]

cTypeToHs :: C.Type -> TH.Q TH.Type
cTypeToHs = \case
    C.DirectType typeName _typeQuals _attributes -> pure $ TH.ConT $ typeNameToHs typeName
    C.PtrType ty _typeQuals _attributes -> TH.AppT (TH.ConT ''Ptr) <$> cTypeToHs ty
    C.ArrayType ty _arraySize _typeQuals _attributes -> TH.AppT (TH.ConT ''Ptr) <$> cTypeToHs ty
    C.FunctionType (C.FunType retTy' params' _isVariadic) _attributes -> do
        retTy <- cTypeToHs retTy'
        params <- mapM paramToHs params'
        pure $ foldr (TH.AppT . TH.AppT TH.ArrowT) (TH.AppT (TH.ConT ''IO) retTy) params
    C.FunctionType (C.FunTypeIncomplete _type) _attributes -> error "FunTypeIncomplete unsupported"
    C.TypeDefType (C.TypeDefRef (C.Ident i _ _) _ty _nodeInfo) _typeQuals _attributes -> pure $ TH.ConT $ TH.mkName $ toPascal $ fromAny i
  where
    paramToHs = \case
        C.ParamDecl (C.VarDecl _varName _declAttrs ty) _nodeInfo -> cTypeToHs ty
        C.AbstractParamDecl (C.VarDecl _varName _declAttrs ty) _nodeInfo -> cTypeToHs ty

    typeNameToHs = \case
        C.TyVoid -> ''()
        C.TyIntegral intType -> case intType of
            C.TyBool -> ''Foreign.C.CBool
            C.TyChar -> ''Foreign.C.CChar
            C.TySChar -> ''Foreign.C.CSChar
            C.TyUChar -> ''Foreign.C.CUChar
            C.TyShort -> ''Foreign.C.CShort
            C.TyUShort -> ''Foreign.C.CUShort
            C.TyInt -> ''Foreign.C.CInt
            C.TyUInt -> ''Foreign.C.CUInt
            C.TyInt128 -> error "TyInt128 unsupported"
            C.TyUInt128 -> error "TyUInt128 unsupported"
            C.TyLong -> ''Foreign.C.CLong
            C.TyULong -> ''Foreign.C.CULong
            C.TyLLong -> ''Foreign.C.CLLong
            C.TyULLong -> ''Foreign.C.CULLong
        C.TyFloating floatType -> case floatType of
            C.TyFloat -> ''Foreign.C.CFloat
            C.TyDouble -> ''Foreign.C.CDouble
            C.TyLDouble -> error "TyLDouble unsupported"
            C.TyFloatN _ _ -> error "TyFloatN unsupported"
        C.TyComplex _floatType -> error "TyComplex unsupported"
        C.TyComp _compTypeRef -> error "TyComp unsupported"
        C.TyEnum _enumTypeRef -> error "TyEnum unsupported"
        C.TyBuiltin _builtinType -> error "TyBuiltin unsupported"
