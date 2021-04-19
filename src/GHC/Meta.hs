{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module GHC.Meta (GHC.Meta.parseType, parseExp, parsePat, metaType, metaExp, metaPat) where

import           Bag
import           BasicTypes
import           Data.ByteString.Char8          ( unpack )
import qualified EnumSet
import           FastString
import           GHC
import qualified Language.Haskell.TH.Syntax    as TH
import           Lexer
import           Module
import           Name
import           Parser
import           RdrHsSyn
import           RdrName
import           SrcLoc
import           StringBuffer
import           Unique

reifyName :: NamedThing n => n -> TH.Name
reifyName thing
  | isExternalName name = reifyExternalName md occ
  | otherwise = TH.mkNameU occ_str (toInteger $ getKey (getUnique name))
 where
  name    = getName thing
  md      = nameModule name
  occ     = nameOccName name
  occ_str = occNameString occ

reifyExternalName :: Module -> OccName -> TH.Name
reifyExternalName m o = mk_varg pkg_str mod_str occ_str where
  pkg_str = unitIdString (moduleUnitId m)
  mod_str = moduleNameString (moduleName m)
  occ_str = occNameString o
  mk_varg | isDataOcc o = TH.mkNameG_d
          | isVarOcc o  = TH.mkNameG_v
          | isTcOcc o   = TH.mkNameG_tc
          | otherwise   = error "reifyName"

metaName :: RdrName -> TH.Name
metaName = \case
  (Unqual o) -> TH.Name (TH.OccName (occNameString o)) TH.NameS
  (Qual m o) -> TH.Name (TH.OccName (occNameString o))
                        (TH.NameQ (TH.ModName (moduleNameString m)))
  (Orig m o) -> reifyExternalName m o
  (Exact n ) -> reifyName n

metaLit :: HsLit GhcPs -> TH.Lit
metaLit = \case
  (HsChar       _ c) -> TH.CharL c
  (HsCharPrim   _ c) -> TH.CharL c
  (HsString     _ f) -> TH.StringL (unpackFS f)
  (HsStringPrim _ b) -> TH.StringL (unpack b)
  (HsInt        _ i) -> TH.IntegerL (il_value i)
  (HsIntPrim    _ i) -> TH.IntPrimL i
  (HsWordPrim   _ i) -> TH.WordPrimL i
  (HsInt64Prim  _ i) -> TH.IntPrimL i
  (HsWord64Prim _ i) -> TH.WordPrimL i
  (HsInteger _ i _ ) -> TH.IntegerL i
  (HsRat     _ f _ ) -> TH.RationalL (fl_value f)
  (HsFloatPrim  _ f) -> TH.FloatPrimL (fl_value f)
  (HsDoublePrim _ f) -> TH.DoublePrimL (fl_value f)

metaPat :: Pat GhcPs -> TH.Pat
metaPat = \case
  (WildPat _              ) -> TH.WildP
  (VarPat  _ (L _ n)      ) -> TH.VarP (metaName n)
  (LazyPat _ (L _ p)      ) -> TH.TildeP (metaPat p)
  (AsPat _ (L _ n) (L _ p)) -> TH.AsP (metaName n) (metaPat p)
  (ParPat  _ (L _ p)      ) -> metaPat p
  (BangPat _ (L _ p)      ) -> TH.BangP (metaPat p)
  (ListPat _ pats         ) -> TH.ListP (map (\(L _ p) -> metaPat p) pats)
  (TuplePat _ pats Boxed  ) -> TH.TupP (map (\(L _ p) -> metaPat p) pats)
  (TuplePat _ pats Unboxed) ->
    TH.UnboxedTupP (map (\(L _ p) -> metaPat p) pats)
  (SumPat _ (L _ p) alt arity) -> TH.UnboxedSumP (metaPat p) alt arity
  (ConPatIn (L _ n) info     ) -> case info of
    (PrefixCon args) -> TH.ConP (metaName n) (map (\(L _ p) -> metaPat p) args)
    (RecCon (HsRecFields flds _)) -> TH.RecP
      (metaName n)
      (map
        (\(L _ (HsRecField (L _ (FieldOcc _ (L _ n'))) (L _ arg) _)) ->
          (metaName n', metaPat arg)
        )
        flds
      )
    (InfixCon (L _ p1) (L _ p2)) ->
      TH.InfixP (metaPat p1) (metaName n) (metaPat p2)
  -- (ConPatOut gsc l_t l_v l_v3 t hxgpphgpxgpp h) -> error "Out"
  (ViewPat _ (L _ x) (L _ p)       ) -> TH.ViewP (metaExp x) (metaPat p)
  -- (SplicePat _ hgp) -> _
  (LitPat _ lit                    ) -> TH.LitP (metaLit lit)
  (NPat _ (L _ (OverLit _ v _)) _ _) -> case v of
    (HsIntegral   i) -> TH.LitP (TH.IntegerL (il_value i))
    (HsFractional f) -> TH.LitP (TH.RationalL (fl_value f))
    -- (HsIsString s f) -> _ -- TH._
  -- (NPlusKPat _ gsigp gshgp hgp sgp sgp5) -> _
  (SigPat _ (L _ p) (HsWC _ (HsIB _ (L _ t)))) ->
    TH.SigP (metaPat p) (metaType t)

unboxedSort :: HsTupleSort -> Bool
unboxedSort HsUnboxedTuple = True
unboxedSort _              = False

metaTyVarBndr :: HsTyVarBndr GhcPs -> TH.TyVarBndr
metaTyVarBndr (UserTyVar _ (L _ n)) = TH.PlainTV (metaName n)
metaTyVarBndr (KindedTyVar _ (L _ n) (L _ k)) =
  TH.KindedTV (metaName n) (metaType k)

metaType :: HsType GhcPs -> TH.Type
metaType = \case
  (HsForAllTy _ ForallInvis bndrs (L _ (HsQualTy _ (L _ ctx) (L _ t)))) ->
    TH.ForallT (map (\(L _ bndr) -> metaTyVarBndr bndr) bndrs)
               (map (\(L _ c) -> metaType c) ctx)
               (metaType t)
  (HsForAllTy _ ForallInvis bndrs (L _ t)) ->
    TH.ForallT (map (\(L _ bndr) -> metaTyVarBndr bndr) bndrs) [] (metaType t)
  (HsForAllTy _ ForallVis bndrs (L _ t)) ->
    TH.ForallVisT (map (\(L _ bndr) -> metaTyVarBndr bndr) bndrs) (metaType t)
  (HsQualTy _ (L _ ctx) (L _ t)) ->
    TH.ForallT [] (map (\(L _ c) -> metaType c) ctx) (metaType t)
  (HsTyVar     _ NotPromoted (L _ n )) -> TH.VarT (metaName n) -- TODO ConE
  (HsTyVar     _ IsPromoted  (L _ n )) -> TH.PromotedT (metaName n)
  (HsAppTy     _ (L _ t1)    (L _ t2)) -> TH.AppT (metaType t1) (metaType t2)
  (HsAppKindTy _ (L _ t )    (L _ k )) -> TH.AppKindT (metaType t) (metaType k)
  (HsFunTy _ (L _ t1) (L _ t2)) ->
    TH.AppT (TH.AppT TH.ArrowT (metaType t1)) (metaType t2)
  (HsListTy _ (L _ t)    ) -> TH.AppT TH.ListT (metaType t)
  (HsTupleTy _ tupSort ts) -> foldl
    TH.AppT
    ((if unboxedSort tupSort then TH.UnboxedTupleT else TH.TupleT) (length ts))
    (map (\(L _ t) -> metaType t) ts)
  (HsSumTy _ ts) -> foldl TH.AppT
                          (TH.UnboxedSumT (length ts))
                          (map (\(L _ t) -> metaType t) ts)
  (HsOpTy _ (L _ t1) (L _ n) (L _ t3)) ->
    TH.InfixT (metaType t1) (metaName n) (metaType t3)
  (HsParTy _ (L _ t)) -> metaType t
  (HsIParamTy _ (L _ (HsIPName f)) (L _ t)) ->
    TH.ImplicitParamT (unpackFS f) (metaType t)
  (HsStarTy _ _                         ) -> TH.StarT
  (HsKindSig        _ (L _ t)    (L _ k)) -> TH.SigT (metaType t) (metaType k)
  -- (HsSpliceTy _ hgp              ) -> _
  -- (HsDocTy  xgp gshgp gsh          ) -> _
  -- (HsBangTy xgp h     gshgp        ) -> _
  -- (HsRecTy xgp l_gscgp             ) -> _
  (HsExplicitListTy _ IsPromoted ts     ) -> foldr
    (\(L _ t) -> TH.AppT (TH.AppT TH.PromotedConsT (metaType t)))
    TH.PromotedNilT
    ts
  (HsExplicitListTy _ NotPromoted ts) ->
    foldl TH.AppT TH.ListT (map (\(L _ t) -> metaType t) ts)
  (HsExplicitTupleTy _ ts) -> foldl TH.AppT
                                    (TH.PromotedTupleT (length ts))
                                    (map (\(L _ t) -> metaType t) ts)
  (HsTyLit _ h) -> TH.LitT $ case h of
    (HsNumTy _ i) -> TH.NumTyLit i
    (HsStrTy _ f) -> TH.StrTyLit (unpackFS f)
  (HsWildCardTy _) -> TH.WildCardT

metaClause :: Match GhcPs (LHsExpr GhcPs) -> TH.Clause
metaClause (Match _ _ pats (GRHSs _ grhss (L _ bnds))) = TH.Clause
  (map (\(L _ p) -> metaPat p) pats)
  (metaGRHSs grhss)
  (metaBinds bnds)

metaGRHSs :: [LGRHS GhcPs (LHsExpr GhcPs)] -> TH.Body
metaGRHSs [L _ (GRHS _ [] (L _ rhs))] = TH.NormalB (metaExp rhs)
metaGRHSs grhss                       = TH.GuardedB $ map
  (\(L _ (GRHS _ stmts (L _ x))) ->
    (TH.PatG (map (\(L _ stmt) -> metaStmt stmt) stmts), metaExp x)
  )
  grhss

metaBinds :: HsLocalBinds GhcPs -> [TH.Dec]
metaBinds = \case
  (HsValBinds _ (ValBinds _ bindsBag _)) -> map
    (\(L _ bnd) -> case bnd of
      (FunBind _ (L _ n) (MG _ (L _ mtchs) _) _ _) ->
        TH.FunD (metaName n) (map (\(L _ mtch) -> metaClause mtch) mtchs)
      (PatBind _ (L _ p) (GRHSs _ grhss (L _ bnds)) _) ->
        TH.ValD (metaPat p) (metaGRHSs grhss) (metaBinds bnds)
      (VarBind _ n (L _ x) _) ->
        TH.ValD (TH.VarP (metaName n)) (TH.NormalB (metaExp x)) []
      (PatSynBind _ (PSB _ (L _ n) details (L _ p) dir)) -> TH.PatSynD
        (metaName n)
        (case details of
          (PrefixCon ns) -> TH.PrefixPatSyn (map (\(L _ n') -> metaName n') ns)
          (RecCon flds) -> TH.RecordPatSyn
            (map
              (\case
                (RecordPatSynField (L _ n') _) -> metaName n'
              )
              flds
            )
          (InfixCon (L _ n1) (L _ n2)) ->
            TH.InfixPatSyn (metaName n1) (metaName n2)
        )
        (metaPatSynDir dir)
        (metaPat p)
    )
    (bagToList bindsBag)
  (HsIPBinds _ (IPBinds _ ipbnds)) -> map
    (\(L _ (IPBind _ eitherName (L _ x))) -> TH.ImplicitParamBindD
      (either (\(L _ (HsIPName f)) -> unpackFS f)
              (const (error "Right case not handled"))
              eitherName
      )
      (metaExp x)
    )
    ipbnds
  (EmptyLocalBinds _) -> []

metaPatSynDir :: HsPatSynDir GhcPs -> TH.PatSynDir
metaPatSynDir Unidirectional        = TH.Unidir
metaPatSynDir ImplicitBidirectional = TH.ImplBidir
metaPatSynDir (ExplicitBidirectional (MG _ (L _ cls) _)) =
  TH.ExplBidir (map (\(L _ cl) -> metaClause cl) cls)

metaStmt :: Stmt GhcPs (LHsExpr GhcPs) -> TH.Stmt
metaStmt = \case
  (LastStmt _ (L _ x) _ _        ) -> TH.NoBindS (metaExp x)
  (BindStmt _ (L _ p) (L _ x) _ _) -> TH.BindS (metaPat p) (metaExp x)
  -- (ApplicativeStmt _ l_p_sgpagp msgp) -> _
  (BodyStmt _ (L _ x) _ _        ) -> TH.NoBindS (metaExp x)
  (LetStmt _ (L _ locBnds)       ) -> TH.LetS (metaBinds locBnds)
  -- (ParStmt _ l_pgpgp hgp _) -> _
  -- (TransStmt _ t l_gssgpgpgshgp l_p_igpigp gshgp mgshgp _
  --            _ hgp)
  --   -> _
  (RecStmt _ stmts _ _ _ _ _) ->
    TH.RecS (map (\(L _ stmt) -> metaStmt stmt) stmts)

metaCase :: Match GhcPs (LHsExpr GhcPs) -> TH.Match
metaCase (Match _ _ [L _ p] (GRHSs _ grhss (L _ bnds))) =
  TH.Match (metaPat p) (metaGRHSs grhss) (metaBinds bnds)

metaExp :: HsExpr GhcPs -> TH.Exp
metaExp = \case
  (HsVar _ (L _ n)) -> TH.VarE (metaName n)
  (HsUnboundVar _ u) ->
    TH.UnboundVarE (TH.mkName (occNameString (unboundVarOcc u)))
  -- (HsConLikeOut _ c        ) -> TH.ConE (reifyName (conLikeName c))
  (HsRecFld _ aa           ) -> TH.VarE (metaName (rdrNameAmbiguousFieldOcc aa))
  (HsOverLabel _ _ f       ) -> TH.LabelE (unpackFS f)
  (HsIPVar   _ (HsIPName f)) -> TH.ImplicitParamVarE (unpackFS f)
  (HsOverLit _ ol          ) -> TH.LitE $ case ol_val ol of
    HsIntegral   il -> TH.IntegerL (il_value il)
    HsFractional fl -> TH.RationalL (fl_value fl)
    HsIsString _ f  -> TH.StringL (unpackFS f)
  (HsLit _ lit) -> TH.LitE (metaLit lit)
  (HsLam _ (MG _ (L _ [L _ (Match _ _ pats (GRHSs _ [L _ (GRHS _ _ (L _ rhs))] _))]) _))
    -> TH.LamE (map (\(L _ p) -> metaPat p) pats) (metaExp rhs)
  (HsLam _ _) -> error "Unexpected lambda"
  (HsLamCase _ (MG _ (L _ mtchs) _)) ->
    TH.LamCaseE (map (\(L _ mtch) -> metaCase mtch) mtchs)
  (HsApp _ (L _ x1) (L _ x2)) -> TH.AppE (metaExp x1) (metaExp x2)
  (HsAppType _ (L _ x) (HsWC _ (L _ t))) ->
    TH.AppTypeE (metaExp x) (metaType t)
  (OpApp _ (L _ x1) (L _ x2) (L _ x3)) ->
    TH.InfixE (Just (metaExp x1)) (metaExp x2) (Just (metaExp x3))
  (NegApp _ (L _ x) _) -> TH.AppE (TH.VarE 'negate) (metaExp x)
  (HsPar _ (L _ x)   ) -> metaExp x
  (SectionL _ (L _ x1) (L _ x2)) ->
    TH.InfixE (Just (metaExp x1)) (metaExp x2) Nothing
  (SectionR _ (L _ x2) (L _ x3)) ->
    TH.InfixE Nothing (metaExp x2) (Just (metaExp x3))
  (ExplicitTuple _ xs Boxed) -> TH.TupE
    (map
      (\case
        L _ (Present _ (L _ x)) -> Just (metaExp x)
        L _ (Missing _        ) -> Nothing
      )
      xs
    )
  (ExplicitTuple _ xs Unboxed) -> TH.UnboxedTupE
    (map
      (\case
        L _ (Present _ (L _ x)) -> Just (metaExp x)
        L _ (Missing _        ) -> Nothing
      )
      xs
    )
  (ExplicitSum _ alt arity (L _ x)) -> TH.UnboxedSumE (metaExp x) alt arity
  (HsCase _ (L _ x) (MG _ (L _ mtchs) _)) ->
    TH.CaseE (metaExp x) (map (\(L _ mtch) -> metaCase mtch) mtchs)
  (HsIf _ _ (L _ x1) (L _ x2) (L _ x3)) ->
    TH.CondE (metaExp x1) (metaExp x2) (metaExp x3)
  (HsMultiIf _ grhss) -> TH.MultiIfE
    (map
      (\(L _ (GRHS _ grds (L _ x))) ->
        (TH.PatG (map (\(L _ grd) -> metaStmt grd) grds), metaExp x)
      )
      grhss
    )
  (HsLet _ (L _ bnds) (L _ x)) -> TH.LetE (metaBinds bnds) (metaExp x)
  (HsDo _ DoExpr (L _ stmts)) ->
    TH.DoE (map (\(L _ stmt) -> metaStmt stmt) stmts)
  (HsDo _ MDoExpr (L _ stmts)) ->
    TH.MDoE (map (\(L _ stmt) -> metaStmt stmt) stmts)
  (HsDo _ _ (L _ stmts)) -> TH.DoE (map (\(L _ stmt) -> metaStmt stmt) stmts)
  (ExplicitList _ _ xs) -> TH.ListE (map (\(L _ x) -> metaExp x) xs)
  (RecordCon _ (L _ n) (HsRecFields flds Nothing)) -> TH.RecConE
    (metaName n)
    (map
      (\(L _ (HsRecField (L _ (FieldOcc _ (L _ lbl))) (L _ arg) _)) ->
        (metaName lbl, metaExp arg)
      )
      flds
    )
  (RecordUpd _ (L _ x) updFlds) -> TH.RecUpdE
    (metaExp x)
    (map
      (\(L _ (HsRecField (L _ afo) (L _ x') _)) ->
        (metaName (rdrNameAmbiguousFieldOcc afo), metaExp x')
      )
      updFlds
    )
  (ExprWithTySig _ (L _ x) (HsWC _ (HsIB _ (L _ t)))) ->
    TH.SigE (metaExp x) (metaType t)
  (ArithSeq _ _ aa) -> TH.ArithSeqE $ case aa of
    (From (L _ l)            ) -> TH.FromR (metaExp l)
    (FromThen (L _ l) (L _ t)) -> TH.FromThenR (metaExp l) (metaExp t)
    (FromTo   (L _ l) (L _ r)) -> TH.FromToR (metaExp l) (metaExp r)
    (FromThenTo (L _ l) (L _ t) (L _ r)) ->
      TH.FromThenToR (metaExp l) (metaExp t) (metaExp r)

emptyParserFlags :: ParserFlags
emptyParserFlags = mkParserFlags' EnumSet.empty
                                  EnumSet.empty
                                  (stringToUnitId "test")
                                  False
                                  False
                                  False
                                  False

initPState :: String -> PState
initPState x = mkPStatePure emptyParserFlags
                            (stringToStringBuffer x)
                            (mkRealSrcLoc (fsLit "test") 0 0)

parseXY :: P (Located x) -> (x -> y) -> String -> Maybe y
parseXY p meta str =
  case unP p (initPState str) of
    POk _ (L _ x) -> Just (meta x)
    PFailed _      -> Nothing

parseExp :: String -> Maybe TH.Exp
parseExp = parseXY (runECP_P @(HsExpr _) =<< parseExpression) metaExp

parseType :: String -> Maybe TH.Type
parseType = parseXY Parser.parseType metaType

parsePat :: String -> Maybe TH.Pat
parsePat = parseXY parsePattern metaPat