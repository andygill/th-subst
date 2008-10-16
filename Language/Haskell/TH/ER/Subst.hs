{-# LANGUAGE ParallelListComp #-}

module Language.Haskell.TH.ER.Subst where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Language.ER.Rewrite

import Control.Monad
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List
import qualified Data.Map as Map

--import Debug.Trace

------------------------------------------------------------------------------

type SubstRewrite  i s = Rewrite Q i Dec s
type SubstRewriteM i s = RewriteM Q i Dec s

class (Show s) => Subst s where
  -- |rewrite a specific Node
  substNodeM :: SubstEnv i -> s -> SubstRewriteM i s

  -- |add a rewrite at this type to our env.
  addSubstEnv :: SubstRewrite i s -> SubstEnv i -> SubstEnv i
  addSubstEnv _fn _env = error "addSubstEnv: no match at this type"

  -- |get the (optional) rewrite at this type.
  getSubstRewrite :: SubstEnv i -> SubstRewrite i s
  getSubstRewrite _env = nullRewrite

  -- |This matches free vars in the 2nd argument (template) to 
  -- values extracted from the 3rd argument (the concrete code).
  --
  -- The 1st argument is for locally bound alpha-conversions.
  --
  -- Example:
  --      2nd arg                 3rd arg
  --    (case e of		(case e2 of
  --      (x:xs) -> x) 		   (x2:xs2) -> x2)
  --
  -- Here, when you find x in the 2nd arg, you need to look for x2 
  -- in the 3rd argument.
  --
  matchNode :: Map.Map Name Name -> s -> s -> Maybe (Map.Map Name Exp)

class Free s where
  -- what is free in this expression?
  freeVarNames :: s -> Set Name
 
class Bind s where
  -- what does this 'expression/pattern' bind?
   boundVarNames :: s -> Set Name

------------------------------------------------------------------------------

data SubstOrder = Prefix Bool -- recurse on the result of any rewrite
     		| Postfix     -- apply subst's after the treewalk
		| Here	      -- only apply in one location
		| Path Int SubstOrder 
		       	      -- dig down a specific path
		deriving (Eq, Ord, Show)

-- extend for more rewrites a different types.

data SubstEnv i = SubstEnv
	      { substWithDec     :: SubstRewrite i Dec
	      , substWithDecs    :: SubstRewrite i Decs
	      , substWithExp     :: SubstRewrite i Exp
	      , substWithClause  :: SubstRewrite i Clause
	      , substWithMatch   :: SubstRewrite i Match
	      , substWithName    :: SubstRewrite i Name
	      , substOrder       :: SubstOrder
--	      , substPrune       :: [Int]	  -- ^ starting location of rewrites
	      }

emptySubstEnv = SubstEnv
	      { substWithDec =  nullRewrite
	      , substWithDecs =  nullRewrite
	      , substWithExp =  nullRewrite
	      , substWithClause =  nullRewrite
	      , substWithMatch   =  nullRewrite
	      , substWithName    =  nullRewrite
	      , substOrder = Prefix False
--	      , substPrune  = []
	      }

------------------------------------------------------------------------------
{-
data MatchEnv = MatchEnv
     	      { varMatch :: Map.Map Name Exp	-- matching of expression names
	      , patMatch :: Map.Map Name Name	-- matching on pattern names
	      }

singleVarMatch :: Name -> Exp -> MatchEnv
singleVarMatch name exp = Map.singleton name exp
singlePatMatch :: Name -> Pat -> MatchEnv
singlePatMatch name pat = Map.singleton name pat

-- unionMatchEnv :: MatchEnv -> MatchEnv -> MatchEnv
-- unionMatchEnv 
-}
------------------------------------------------------------------------------

-- | We redirect all [Dec] via this type (Decs)
-- because we want to have [Dec] -> [Dec] rewrites.

-- non-top levels Decs
data Decs = Decs [Dec] deriving Show

data Stmts = Stmts { unStmts :: [Stmt] }
      deriving Show	 -- because stmts have binding from element to element

instance Subst Dec where 
  addSubstEnv fn env = env { substWithDec = fn }
  getSubstRewrite env = substWithDec env 

  substNodeM env (FunD name clauses) = liftM2 FunD (substM env 0 name)
  	     	       	    	      	       	   (substM env 1 clauses)

  substNodeM env (ValD pat body decs) = liftM3 ValD (substM env 0 pat)
  	     	       	    	      	       	    (substM env 1 body)
						    (substM env 2 decs)
  substNodeM env (SigD name ty) = liftM2 SigD (substM env 0 name)
  	     	       	    	  	      (substM env 1 ty)
   -- TODO
  substNodeM env dec@(DataD {})  = return dec
  substNodeM env dec@(TySynD {})  = return dec
  substNodeM env dec@(InstanceD {})  = return dec
  substNodeM env other          = error $ show other

instance Free Dec where
  freeVarNames (FunD name clauses)  = freeVarNames clauses
  freeVarNames (ValD pat body decs) 
  	     = Set.unions [ freeVarNames body
	       			 , freeVarNames decs
				 ] `Set.difference` boundVarNames pat
  freeVarNames (SigD name ty) = Set.empty

-- TODO: seperate classes for boundVarName and freeVarName

instance Bind Dec where
  boundVarNames (FunD name _)  = Set.singleton name
  boundVarNames (ValD pat _ _) = boundVarNames pat
  boundVarNames (SigD name _)  = Set.singleton name

instance Subst Exp where
  addSubstEnv fn env = env { substWithExp = fn }
  getSubstRewrite env = substWithExp env 

  substNodeM env (VarE name)  = liftM VarE (substM env 0 name)
  substNodeM env (ConE name)  = liftM ConE (substM env 0 name)
  substNodeM env (LitE lit)   = liftM LitE (substM env 0 lit)
  substNodeM env (AppE e1 e2) = liftM2 AppE (substM env 0 e1)
  	     	       	      	       	    (substM env 1 e2)

  substNodeM env (InfixE m_e1 e2 m_e3) 
  	     = liftM3 InfixE  	 (substM env 0 m_e1)
	       	      		 (substM env 1 e2)
	       	      		 (substM env 2 m_e3)
  substNodeM env (LamE pats exp) 
  	     = liftM2 LamE   	 (substM env 0 pats)
	       	     		 (substM env 1 exp)
  substNodeM env (TupE exps) 
  	     = liftM TupE (substM env 0 exps)

  substNodeM env (CondE e1 e2 e3)
  	     = liftM3 CondE  	 (substM env 0 e1)
	       	      		 (substM env 1 e2)
	       	      		 (substM env 2 e3)
  substNodeM env (LetE decs exp) 
  	     = addBindingsM decs
	     $ liftM2 LetE  	 (substM env 0 decs)
	       	      	   	 (substM env 1 exp)
  substNodeM env (CaseE exp matches) 
  	     = liftM2 CaseE 	 (substM env 0 exp)
	       	      		 (substM env 1 matches)
  substNodeM env (DoE stmts) 
  	     = liftM (DoE . unStmts)
	       	     	       	 (substM env 0 (Stmts stmts))
  substNodeM env (CompE stmts) 
  	     = liftM CompE       (substM env 0 stmts)
  substNodeM env (ArithSeqE range) 
  	     = liftM ArithSeqE   (substM env 0 range)
  substNodeM env (ListE exps) 
  	     = liftM ListE 	 (substM env 0 exps)
  substNodeM env (SigE exp ty)
  	     = liftM2 SigE 	 (substM env 0 exp)
	       	      		 (substM env 1 ty)
  substNodeM env (RecConE name fieldexps) 
  	     = liftM2 RecConE    (substM env 0 name)
	       			 (substM env 1 fieldexps)
  substNodeM env (RecUpdE exp fieldexps) 
  	     = liftM2 RecUpdE    (substM env 0 exp)
	       			 (substM env 1 fieldexps)

  matchNode env (VarE name) any = 
    case nameModule name of
      Just "Language.Haskell.ER.Frees" -> return $ name `Map.singleton` any
      _ -> case any of
      	     VarE name' | name == name'
		  	       -> return $ Map.empty
                        | otherwise 
			       -> -- trace (show (name,name',env,"LOOKUP")) $
			       	   case Map.lookup name env of
--				    Just name'' | trace (show (name,name',name'')) False -> undefined
				    Just name'' | name' == name'' 
				      -> return $ Map.empty	  -- good match
			       	    _ -> fail ""
	     _ -> fail $ "bad match with : " ++ show name

  matchNode env 
  	    (ConE name1) 
  	    (ConE name2)   | name1 == name2
	    	  	   = return $ Map.empty
  matchNode env
  	    (LitE lit1) 
  	    (LitE lit2)   | lit1 == lit2
	    	  	   = return $ Map.empty
  matchNode env
  	    (AppE e11 e12)
  	    (AppE e21 e22)  = liftM2 Map.union
	    	      	      	    (matchNode env e11 e21)
	    	      	      	    (matchNode env e12 e22)
  matchNode env
  	    (InfixE m_e11 e12 m_e13) 
  	     (InfixE m_e21 e22 m_e23) 
  	     = liftM3 (\ a b c -> Map.unions [a,b,c])
	       	      	         (matchNode env m_e11 m_e21)
	       	      	         (matchNode env e12 e22)
	       	      	         (matchNode env m_e13 m_e23)
  matchNode env
  	    (DoE ((BindS p1 e1) : stmts1))
  	    (DoE ((BindS p2 e2) : stmts2))
	    = do env' <- matchPat p1 p2
	      	 liftM2 Map.union
	      	    (matchNode env e1 e2)
		    (matchNode (env' `Map.union` env) (DoE stmts1) (DoE stmts2))
  matchNode env
  	    (DoE ((NoBindS e1) : stmts1))
  	    (DoE ((NoBindS e2) : stmts2))
	    = liftM2 Map.union
	      	    (matchNode env e1 e2)
		    (matchNode env (DoE stmts1) (DoE stmts2))
  matchNode env
  	    (DoE [])
  	    (DoE [])
	    = return $ Map.empty

  matchNode env 
  	    (LamE ps1 e1)
            (LamE ps2 e2) = do
	    	  env' <- matchPats ps1 ps2
	    	  matchNode (env' `Map.union` env) e1 e2 
  matchNode env 
  	    (CaseE e1 matches1) 
            (CaseE e2 matches2) 
  	    	      = liftM2 Map.union
	    	     	      	    (matchNode env e1 e2)
	    	      	      	    (matchNode env matches1 matches2)

  matchNode env
  	    (ListE es1)
	    (ListE es2)
	    	   = matchNodes es1 es2
    where
	matchNodes [] [] = return $ Map.empty
	matchNodes (e1:es1) (e2:es2) =
	    	    liftM2 Map.union 
		     	   	  (matchNode env e1 e2)
				  (matchNodes es1 es2)
	matchNodes _ _ = fail "no match"

  matchNode _ _ _ = fail "no match"


instance Free Exp where
  freeVarNames (VarE name)  = Set.singleton name
  freeVarNames (ConE name)  = Set.empty			-- different namespace (ish)!
  freeVarNames (LitE lit)   = Set.empty
  freeVarNames (AppE e1 e2) 
  	     = Set.unions [ freeVarNames e1
	       			 , freeVarNames e2
				 ]
  freeVarNames (InfixE m_e1 e2 m_e3) 
  	     = Set.unions [ freeVarNames m_e1
	       			 , freeVarNames e2
	       			 , freeVarNames m_e3
				 ]
  freeVarNames (LamE pats exp) 
  	     = freeVarNames exp `Set.difference` boundVarNames pats

  freeVarNames (TupE exps) 
  	     = Set.unions [ freeVarNames exps 
	       			 ]

  freeVarNames (CondE e1 e2 e3)
  	     = Set.unions [ freeVarNames e1
	       			 , freeVarNames e2
	       			 , freeVarNames e3
				 ]
  freeVarNames (LetE decs exp) 
  	     = Set.unions [ freeVarNames decs
	       			 , freeVarNames exp
				 ] `Set.difference` boundVarNames decs
  freeVarNames (CaseE exp matches) 
  	     = Set.unions [ freeVarNames exp
	       	      		 , freeVarNames matches
				 ]
  freeVarNames (DoE stmts) 
  	     = freeVarNames (Stmts stmts)
  freeVarNames (CompE stmts) 
  	     = Set.unions [ freeVarNames stmts ]
  freeVarNames (ArithSeqE range) 
  	     = Set.unions [ freeVarNames range ]
  freeVarNames (ListE exps) 
  	     = Set.unions [ freeVarNames exps ]
  freeVarNames (SigE exp ty)
  	     = Set.unions [ freeVarNames exp ]
  freeVarNames (RecConE name fieldexps) 
  	     = Set.unions [ freeVarNames name
	       			 , freeVarNames fieldexps
				 ]
  freeVarNames (RecUpdE exp fieldexps) 
  	     = Set.unions [ freeVarNames exp
	       			 , freeVarNames fieldexps
				 ]


instance Subst Con where {}
instance Subst Strict where {}

instance Subst Type where 
  -- for now
  substNodeM env a = return a

instance Subst Match where
  addSubstEnv fn env = env { substWithMatch = fn }
  getSubstRewrite env = substWithMatch env 

  substNodeM env (Match pat exp binds) 
  	     = liftM3 Match      (substM env 0 pat)
	       			 (substM env 1 exp)
	       			 (substM env 2 binds)
{-
  -- for debugging
  matchNode env
  	    matches1
	    matches2
	    | trace (show (env,matches1,matches2)) False = undefined
-}
  matchNode env
  	    (Match pat1 body1 [])	-- for now []
  	    (Match pat2 body2 [])
	    = do env' <- matchPat pat1 pat2
	         matchNode (env' `Map.union` env)
		 	   body1
			   body2
  matchNode env _ _ = fail "matchNode"

instance Free Match where
  freeVarNames (Match pat body decs) 
  	      = Set.unions [ freeVarNames body
	      			  , freeVarNames decs
				  ] `Set.difference` 
	        Set.unions [ boundVarNames decs
				  , boundVarNames pat
				  ]
  	     	 
	    


instance Subst Clause where
  addSubstEnv fn env = env { substWithClause = fn }
  getSubstRewrite env = substWithClause env 

  substNodeM env (Clause pats body decs) = 
  	       liftM3 Clause  	 (substM env 0 pats)
	       	      		 (substM env 1 body)
	       	      		 (substM env 2 decs)


instance Free Clause where
  freeVarNames (Clause pats body decs) 
  	      = Set.unions [ freeVarNames body
	      			  , freeVarNames decs
				  ] `Set.difference` 
	        Set.unions [ boundVarNames decs
				  , boundVarNames pats
				  ]

instance Subst Body where 
  substNodeM env (NormalB exp)        = liftM NormalB (substM env 0 exp)
  substNodeM env (GuardedB guardeds) = liftM GuardedB (substM env 0 guardeds)

  matchNode env
  	    (NormalB e1)
  	    (NormalB e2) 
	    = matchNode env e1 e2
  matchNode env _ _ = fail "matchNode"

instance Free Body where
  freeVarNames (NormalB exp) = freeVarNames exp
  freeVarNames (GuardedB guardeds) = freeVarNames guardeds

instance Subst Guard where 
  substNodeM env (NormalG exp)        = liftM NormalG (substM env 0 exp)
  substNodeM env e = error $ "substNodeM: " ++ show e

instance Free Guard where
  freeVarNames (NormalG exp) = freeVarNames exp

instance Subst Stmts where
  substNodeM env (Stmts stmts) = 
      liftM Stmts $ sequence [ substM env n e 
      	    	    	     | e <- stmts 
			     | env <- envs
			     | n <- [0..]
			     ]
    where
       envs = scanl (\ env stmt -> env) env stmts

instance Free Stmts where
  freeVarNames (Stmts stmts) = 
  	       freeVarNames stmts `Set.difference` boundVarNames stmts

instance Subst Stmt where
  substNodeM env (BindS pat exp) = liftM2 BindS (substM env 0 pat)
  	     	 	    	   	 	(substM env 1 exp)
  substNodeM env (LetS decs)     = liftM LetS (substM env 0 decs)
  substNodeM env (NoBindS exp)   = liftM NoBindS (substM env 0 exp)

  matchNode env 
  	    (BindS (VarP v1) e1)
  	    (BindS (VarP v2) e2)
	    = matchNode (Map.insert v2 v1 env) e1 e2
	      		-- map real var to eq rhs var
  matchNode env 
  	    (NoBindS e1)
  	    (NoBindS e2)
	    = matchNode env e1 e2

  matchNode _ _ _ = fail "no match"

instance Free Stmt where
  freeVarNames (BindS pat exp) = 
        freeVarNames exp `Set.difference` boundVarNames pat
  freeVarNames (LetS decs)     =
        freeVarNames decs `Set.difference` boundVarNames decs
  freeVarNames (NoBindS exp)  = freeVarNames exp

instance Bind Stmt where
  boundVarNames (BindS pat exp) = boundVarNames pat
  boundVarNames (LetS decs)     = boundVarNames decs
  boundVarNames (NoBindS exp)   = Set.empty

instance Subst Range where 
  substNodeM env (FromR e1) = liftM FromR (substM env 0 e1)
  substNodeM env (FromThenR e1 e2) = liftM2 FromThenR (substM env 0 e1)
  	     	 	       	     	    	      (substM env 1 e2)
  substNodeM env (FromToR e1 e2) = liftM2 FromToR (substM env 0 e1)
  	     	 	       	     	    	      (substM env 1 e2)
  substNodeM env (FromThenToR e1 e2 e3) = liftM3 FromThenToR (substM env 0 e1)
  	     	 	       	     	    	      (substM env 1 e2)
  	     	 	       	     	    	      (substM env 2 e3)

instance Free Range where {}

instance Subst Lit where 
  substNodeM env e = return e

instance Subst Pat where
  substNodeM env (VarP name) = liftM VarP (substM env 0 name)
  substNodeM env (ConP name pats) = liftM2 ConP (substM env 0 name)
  	     	       	    	    	        (substM env 1 pats)
  substNodeM env (WildP) = return $ WildP
  substNodeM env (InfixP p1 name p2) = liftM3 InfixP 
  	     	 	      	    	   (substM env 0 p1)
  	     	 	      	    	   (substM env 1 name)
  	     	 	      	    	   (substM env 2 p2)
  substNodeM env (TupP pats) = liftM TupP (substM env 0 pats)
  substNodeM env (LitP lit)  = return $ LitP lit
  substNodeM env e = error $ "substNodeM: " ++ show e

   -- this should be in a seperate class (Bind), 
   -- because is about binding, not freedom.

-- The first argument is an expressions' lhs
-- The second argument is the expression being matched
-- For free variables insider patterns, we map the lhs Name
-- to the expression name.
matchPats :: [Pat] -> [Pat] -> Maybe (Map.Map Name Name)
matchPats (p1:ps1) (p2:ps2) 
	  = liftM2 Map.union
	      	    (matchPat p1 p2)
		    (matchPats ps1 ps2)
matchPats [] [] = return $ Map.empty
matchPats _  _  = fail "matchPats"

matchPat :: Pat -> Pat -> Maybe (Map.Map Name Name)
matchPat (VarP n1) 
  	 (VarP n2) = return $ n1 `Map.singleton` n2
matchPat (ConP n1 ps1) 
  	 (ConP n2 ps2) | n1 == n2 = matchPats ps1 ps2
matchPat (InfixP p11 o1 p12)
	 (InfixP p21 o2 p22)
	 | o1 == o2
	 = liftM2 Map.union
	   	  (matchPat p11 p21)
		  (matchPat p12 p22)
  -- Not sure about this; should the 2nd argument also match on vars?
  -- I suppose this depending on the frees.
matchPat (WildP) 
  	 (WildP) = return $ Map.empty
matchPat _ _ = fail "matchPat: ..."

instance Bind Pat where
  boundVarNames (VarP name)      = Set.singleton name
  boundVarNames (ConP name pats) = boundVarNames pats

  boundVarNames (WildP) = Set.empty
  boundVarNames (InfixP p1 name p2)
  	     = Set.unions [ boundVarNames p1
	       			 , boundVarNames p2
				 ]
  boundVarNames (TupP pats)      = boundVarNames pats 
  boundVarNames e = error $ "boundVarNames: " ++ show e

instance Subst Foreign where {}
instance Subst FunDep where  {}

instance Subst Name where 
  addSubstEnv fn env = env { substWithName = fn }
  getSubstRewrite env = substWithName env 

  substNodeM env name = return name

instance Free Name where {}

instance Subst Decs where  
  addSubstEnv fn env = env { substWithDecs = fn }
  getSubstRewrite env = substWithDecs env 

  substNodeM env (Decs decs) 
  	     = addBindingsM decs 
	     $ liftM Decs (substM env 0 decs)

instance Subst Callconv where {}
instance Subst Safety where {}

instance (Subst a) => Subst [a] where 
  substNodeM env es = 
      sequence [ substM env n e | e <- es | n <- [0..]]

  matchNode env
  	    (x1:xs1) 
	    (x2:xs2) = liftM2 Map.union
  	    	     	      (matchNode env x1 x2)
  	    	     	      (matchNode env xs1 xs2)
  matchNode _ [] [] = return $ Map.empty
  matchNode _ _ _ = fail "no match"

instance Free a => Free [a] where
  freeVarNames es  = Set.unions $ map freeVarNames es

instance Bind a => Bind [a] where
  boundVarNames = Set.unions . map boundVarNames


instance (Subst a,Subst b) => Subst (a,b) where 
  substNodeM env (a,b) = liftM2 (,) (substM env 0 a)
  	     	       	            (substM env 1 b)

-- TODO: think hard about this, epecially about FieldExp/Pat
instance (Free a,Free b) => Free (a,b) where 
  freeVarNames (a,b)  = Set.unions [ freeVarNames a
  	       	      			  , freeVarNames b
					  ]

instance (Subst a) => Subst (Maybe a) where 
  substNodeM env Nothing  = return Nothing
  substNodeM env (Just e) = liftM Just $ substM env 0 e

  matchNode env (Just a1) (Just a2) = matchNode env a1 a2
  matchNode _ Nothing Nothing     = return $ Map.empty
  matchNode _ _ _	    	  = fail "matchNode: .."


instance (Free a) => Free (Maybe a) where 
  freeVarNames Nothing  = Set.empty
  freeVarNames (Just a) = freeVarNames a


------------------------------------------------------------------------------

subst :: (Subst s) => SubstEnv i -> SubstRewrite i s
subst env@(SubstEnv { substOrder = Postfix }) =
     substNode env >+> getSubstRewrite env
subst env@(SubstEnv { substOrder = Prefix True }) = 
     getSubstRewrite env >+> substNode env
subst env@(SubstEnv { substOrder = Prefix False }) = 
     getSubstRewrite env >|> substNode env
subst env@(SubstEnv { substOrder = Here }) = 
      getSubstRewrite env
subst env@(SubstEnv { substOrder = Path {} }) =
      substNode env

-- The entry point for the liftMs; includes the indexing
substM :: (Subst s) => SubstEnv i -> Int -> s -> SubstRewriteM i s
--substM env ix s 
--  | trace (show (ix,s)) False = undefined
substM env@(SubstEnv { substOrder = Path path_ix order }) ix s 
  | path_ix == ix = addPathM ix ((subst (env { substOrder = order })) s)
  | otherwise     = return s -- do not follow this path
substM env ix s   = addPathM ix ((subst env) s)

substNode :: (Subst s) => SubstEnv i -> SubstRewrite i s
substNode env = substNodeM env

------------------------------------------------------------------------------

substUsing :: (Subst s,Subst s2) => SubstOrder -> SubstRewrite i s2 -> SubstRewrite i s
substUsing order fn = 
	  subst  (addSubstEnv fn emptySubstEnv 
	    	        { substOrder = order }
		 )

------------------------------------------------------------------------------

