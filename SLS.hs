module SLS
  ( Net
  , Name
  , Instance (..)
  , Netlist  (..)
  , Logic    (..)
  , code
  , test
  ) where

import Data.List
import Math.SMT.Yices.Pipe
import Math.SMT.Yices.Syntax
import Text.Printf

type Net  = String
type Name = String

data Instance
  = PMOS Net Net Net  -- gate, source, drain
  | NMOS Net Net Net  -- gate, source, drain

data Netlist = Netlist Name [Net] [Net] [Instance]  -- name, inputs, outputs, instance

-- Output a Verilog switch level netlist.
code :: Netlist -> IO ()
code (Netlist name ins outs instances) = writeFile (name ++ ".v") $ unlines
  [ "module " ++ name
  , "\t( input  vdd"
  , "\t, input  gnd"
  , unlines [ "\t, input  " ++ name | name <- ins ] ++ unlines [ "\t, output " ++ name | name <- outs ] ++ "\t);"
  , ""
  , unlines [ "wire " ++ name | name <- nub (concatMap nets instances) \\ (["vdd", "gnd"] ++ ins ++ outs) ]
  , unlines $ map instantiate instances
  , "endmodule"
  ]

  where
  nets a = case a of
    PMOS a b c -> [a, b, c]
    NMOS a b c -> [a, b, c]

  instantiate a = case a of
    PMOS gate source drain -> printf "pmos (%s, %s, %s);" drain source gate
    NMOS gate source drain -> printf "nmos (%s, %s, %s);" drain source gate

test :: IO ()
test = code $ Netlist "inverter" ["a"] ["x"]
  [ PMOS "a" "vdd" "x"
  , NMOS "a" "gnd" "x"
  ]

synthesize :: Int -> Int -> [(Name, Logic)] -> IO (Maybe Netlist)
synthesize transitors nets logic
  | transitors < 2 = error "CMOS circuit requires at least 2 transitors."
  | odd transitors = error "CMOS circuit requires an even number of transistors."
  | otherwise = do

data Logic
  = Input Name
  | Const Bool
  | Not Logic
  | And Logic Logic
  | Or  Logic Logic

data Cell = Cell
  { cellName    :: Name
  , cellArea    :: Int
  , cellDelay   :: Int
  , cellOutputs :: [(Name, Logic)]
  }

type Library = [Cell]

lib :: Library
lib =
  [ Cell "not"   0 0 [("x", Not (Input "a"))]
  , Cell "and2"  0 0 [("x", And (Input "a") (Input "b"))]
  , Cell "or2"   0 0 [("x", Or  (Input "a") (Input "b"))]
  , Cell "nand2" 0 0 [("x", Not $ And (Input "a") (Input "b"))]
  , Cell "nor2"  0 0 [("x", Not $ Or  (Input "a") (Input "b"))]
  ]

{-
optimize :: [[Cell]] -> Int -> Int -> [Logic] -> IO [Logic]
optimize fabric maxArea maxDelay block = do
  return ()
-}

{-
-- | Verify a program with k-induction.
verify :: FilePath -> Statement -> IO ()
verify yices program = proveAssertions yices format program [] $ assertions program
  where
  format = "%-" ++ show (maximum' [ length $ pathName $ assertionPath t program | (t, _, _) <- assertions program ]) ++ "s    "

-- | Path of an assertion.
assertionPath :: Int -> Statement -> Path
assertionPath t stmt = case f stmt of
  Nothing -> error $ "theorem not found: " ++ show t
  Just p  -> p
  where
  pair :: Statement -> Statement -> Maybe Path
  pair a b = case (f a, f b) of
    (Just a, _) -> Just a
    (_, Just a) -> Just a
    _ -> Nothing
  f :: Statement -> Maybe Path
  f a = case a of
    Assert t' _ _ | t == t' -> Just []
    Sequence a b -> pair a b
    Branch _ a b -> pair a b
    Label name a -> do
      path <- f a
      return $ name : path
    _ -> Nothing

proveAssertions :: FilePath -> String -> Statement -> [Int] -> [(Int, Int, E Bool)] -> IO ()
proveAssertions _ _ _ _ [] = return ()
proveAssertions yices format program lemmas ((id, k, _) : rest) = do
  printf format name
  hFlush stdout
  env0 <- initEnv program
  pass <- evalStateT (check yices name id lemmas program env0 k) env0
  proveAssertions yices format program (if pass then id : lemmas else lemmas) rest
  where
  name = pathName $ assertionPath id program

data Result = Pass | Fail [ExpY] | Problem

-- | k-induction.
check :: FilePath -> Name -> Int -> [Int] -> Statement -> Env -> Int -> Y Bool
check yices name theorem lemmas program env0 k = do
  mapM_ step [0 .. k - 1]
  resultBasis <- checkBasis yices program env0
  case resultBasis of
    Fail a  -> do
      liftIO (printf "FAILED: disproved basis (see %s.trace)\n" name)
      writeTrace name a
      return False
    Problem -> error "Verify.check1"
    Pass -> do
      step k
      resultStep <- checkStep yices
      case resultStep of
        Fail a  -> do
	  liftIO (printf "inconclusive: unable to proved step (see %s.trace)\n" name)
	  writeTrace name a
	  return False
        Problem -> error "Verify.check2"
        Pass    -> do
	  liftIO $ printf "proved\n"
	  return True
  where
  step :: Int -> Y ()
  step i = do
      addTrace $ Step' i
      sequence_ [ getVar' a >>= addTrace . State' (pathName path) | a@(input, path, _) <- sortBy f $ stmtVars program, not input ]
      sequence_ [ addVar' a >>= addTrace . Input' (pathName path) | a@(input, path, _) <- sortBy f $ stmtVars program,     input ]
      evalStmt theorem lemmas (LitB True) program
  f (_, a, _) (_, b, _) = compare a b

-- | Check induction step.
checkStep :: FilePath -> Y Result
checkStep yices = do
  env <- get
  r <- liftIO $ quickCheckY' yices [] $ reverse (cmds env) ++ [assert env] ++ [CHECK]
  --liftIO $ writeFile "log.txt" $ unlines $ map show $ reverse (cmds env) ++ [assert env] ++ [CHECK]
  return $ result r
  where
  assert env = case asserts env of
    []     -> error "unexpected: induction step needs at least 1 step, got 0"
    [_]    -> error "unexpected: induction step needs at least 2 steps, got 1"
    a : b  -> ASSERT $ AND $ NOT a : b

-- | Check induction basis.
checkBasis :: FilePath -> Statement -> Env -> Y Result
checkBasis yices program env0 = do
  env <- get
  r <- liftIO $ quickCheckY' yices [] $ reverse (cmds env)
          ++ [ASSERT $ NOT $ AND $ asserts env]
          ++ [ ASSERT $ VarE (var env0 a) := evalConst' c | a@(input, _, c) <- stmtVars program, not input ]
          ++ [CHECK]
  return $ result r

result :: ResY -> Result
result a = case a of
  Sat a   -> Fail a
  UnSat _ -> Pass
  InCon _ -> Problem
  _ -> error $ "unexpected yices results: " ++ show a


evalStmt :: Int -> [Int] -> ExpY -> Statement -> Y ()
evalStmt theorem lemmas enabled a = case a of
  Null -> return ()
  Sequence a b -> evalStmt theorem lemmas enabled a >> evalStmt theorem lemmas enabled b
  Assign a b -> assign a b
  Assert id _ a
    | elem id lemmas -> do
      a <- evalExpr a
      addCmd $ ASSERT (enabled :=> a)
    | id == theorem -> do
      a <- evalExpr a
      b <- newBoolVar
      addCmd $ ASSERT (VarE b := (enabled :=> a))
      env <- get
      put env { asserts = VarE b : asserts env }
      addTrace $ Assert' b
    | otherwise -> return ()
  Assume id a
    | elem id lemmas -> do
      a <- evalExpr a
      addCmd $ ASSERT (enabled :=> a)
    | otherwise -> return ()
  Branch a onTrue onFalse -> do
    a <- evalExpr a
    b <- newBoolVar
    addCmd $ ASSERT (VarE b := a)
    env0 <- get
    put env0 { trace = [] }
    evalStmt theorem lemmas (AND [enabled, a]) onTrue
    env1 <- get
    put env1 { trace = [] }
    evalStmt theorem lemmas (AND [enabled, NOT a]) onFalse
    env2 <- get
    put env2 { trace = Branch' b (reverse $ trace env1) (reverse $ trace env2) : trace env0 }
  Label name a -> do
    env0 <- get
    put env0 { trace = [] }
    evalStmt theorem lemmas enabled a
    env1 <- get
    put env1 { trace = Label' name (reverse $ trace env1) : trace env0 }
  where
  assign :: AllE a => V a -> E a -> Y ()
  assign a b = do
    b <- evalExpr b
    aPrev <- getVar a
    aNext <- addVar a
    addCmd $ ASSERT (VarE aNext := IF enabled b (VarE aPrev))
    addTrace $ Assign' (pathName a) aNext

evalExpr :: AllE a => E a -> Y ExpY
evalExpr a = case a of
  Ref a -> getVar a >>= return . VarE
  Const a -> return $ evalConst a
  Add a b ->  do
    a <- evalExpr a
    b <- evalExpr b
    return $ a :+: b
  Sub a b ->  do
    a <- evalExpr a
    b <- evalExpr b
    return $ a :-: b
  Mul a b ->  do
    a <- evalExpr a
    return $ a :*: evalConst b
  Div a b -> do
    a <- evalExpr a
    return $ op a $ evalConst b
    where
    op = case const' b of
      Bool  _ -> undefined
      Int   _ -> DIV
      Float _ -> (:/:)
  Mod a b -> do
    a <- evalExpr a
    return $ MOD a $ evalConst b
  Not a -> evalExpr a >>= return . NOT
  And a b -> do
    a <- evalExpr a
    b <- evalExpr b
    return $ AND [a, b]
  Or a b -> do
    a <- evalExpr a
    b <- evalExpr b
    return $ OR [a, b]
  Eq a b -> do  
    a <- evalExpr a
    b <- evalExpr b
    return $ a := b
  Lt a b -> do  
    a <- evalExpr a
    b <- evalExpr b
    return $ a :< b
  Gt a b -> do  
    a <- evalExpr a
    b <- evalExpr b
    return $ a :> b
  Le a b -> do  
    a <- evalExpr a
    b <- evalExpr b
    return $ a :<= b
  Ge a b -> do  
    a <- evalExpr a
    b <- evalExpr b
    return $ a :>= b
  Mux a b c -> do
    a <- evalExpr a
    b <- evalExpr b
    c <- evalExpr c
    return $ IF a b c

evalConst :: AllE a => a -> ExpY
evalConst = evalConst' . const'

evalConst' :: Const -> ExpY
evalConst' a = case a of
  Bool  a -> LitB a
  Int   a -> LitI $ fromIntegral a
  Float a -> LitR $ toRational a

type Y = StateT Env IO

type Var = String

data Env = Env
  { nextId    :: Int
  , var       :: VarInfo -> Var
  , cmds      :: [CmdY]  -- Commands and variable declarations in reverse order.
  , asserts   :: [ExpY]  -- Assumes 1 assert in a program under verification.
  , trace     :: [Trace] -- Program trace in reverse order.
  }
 
initEnv :: Statement -> IO Env
initEnv program = execStateT (sequence_ [ addVar' a | a@(input, _, _) <- stmtVars program, not input ]) Env
  { nextId  = 0
  , var     = \ v -> error $ "variable not found in environment: " ++ pathName v
  , cmds    = []
  , asserts = []
  , trace   = []
  }

data Trace
  = Step'  Int
  | State'  Name Var
  | Input'  Name Var
  | Assign' Name Var
  | Assert' Var
  | Branch' Var [Trace] [Trace] 
  | Label'  Name [Trace]

addVar' :: VarInfo -> Y String
addVar' v = do
  env <- get
  let name = printf "n%d" $ nextId env
  put env { nextId = nextId env + 1, var = \ a -> if a == v then name else var env a, cmds = DEFINE (name, VarT typ) Nothing : cmds env }
  return name
  where
  typ = case v of
    (_, _, Bool  _) -> "bool"
    (_, _, Int   _) -> "int"
    (_, _, Float _) -> "real"

addVar :: AllE a => V a -> Y String
addVar = addVar' . varInfo

-- | Creates a new boolean variable.  Use for assertions.
newBoolVar :: Y String
newBoolVar = do
  env <- get
  let name = printf "n%d" $ nextId env
  put env { nextId = nextId env + 1, cmds = DEFINE (name, VarT "bool") Nothing : cmds env }
  return name

addCmd :: CmdY -> Y ()
addCmd cmd = do
  env <- get
  put env { cmds = cmd : cmds env }

addTrace :: Trace -> Y ()
addTrace t = do
  env <- get
  put env { trace = t : trace env }

getVar :: AllE a => V a -> Y Var
getVar v = getVar' $ varInfo v

getVar' :: VarInfo -> Y Var
getVar' v = do
  env <- get
  return $ var env $ v

writeTrace :: String -> [ExpY] -> Y ()
writeTrace name table' = do
  env <- get
  let trace' = reverse $ trace env
      format path indent = printf (printf "%%-%ds : %%s" $ maximum' $ 12 : map maxLabelWidth trace') (intercalate "." path) indent
      varFormat :: Name -> String
      varFormat = printf $ printf "%%-%ds" l
        where
        l = maximum $ 0 : map length ([ n | State' n _ <- trace' ] ++ [ n | Input' n _ <- trace' ])
  liftIO $ writeFile (name ++ ".trace") $ concatMap (f varFormat format [] "") trace'
  where
  table = [ (n, if v then "true" else "false") | VarE n := LitB v <- table' ]
       ++ [ (n, show v) | VarE n := LitI v <- table' ]
       ++ [ (n, show v) | VarE n := LitR v <- table' ]

  f :: (String -> String) -> (Path -> String -> String) -> Path -> String -> Trace -> String
  f varFormat format path' indent a = case a of
    Step' n -> "(step " ++ show n ++ ")\n"
    State' path var -> case lookup var table of
      Nothing -> ""
      Just value -> format ["(state)"] indent ++ varFormat path ++ " == " ++ value ++ "\n"
    Input' path var -> case lookup var table of
      Nothing -> ""
      Just value -> format ["(input)"] indent ++ varFormat path ++ " <== " ++ value ++ "\n"
    Assign' path var -> case lookup var table of
      Nothing -> ""
      Just value -> format path' indent ++ path ++ " <== " ++ value ++ "\n"
    Assert' var -> case lookup var table of
      Just "true"  -> format path' indent ++ "theorem assertion passed\n"
      Just "false" -> format path' indent ++ "theorem assertion FAILED\n"
      _ -> ""
    Branch' cond onTrue onFalse -> case lookup cond table of
      Just "true"  -> format path' indent ++ "ifelse true:\n"  ++ concatMap (f varFormat format path' $ "    " ++ indent) onTrue
      Just "false" -> format path' indent ++ "ifelse false:\n" ++ concatMap (f varFormat format path' $ "    " ++ indent) onFalse
      _ -> ""
    Label' name traces -> concatMap (f varFormat format (path' ++ [name]) indent) traces

maxLabelWidth :: Trace -> Int
maxLabelWidth a = case a of
  Branch' _ a b -> maximum' $ map maxLabelWidth $ a ++ b
  Label' a b -> length a + 1 + maximum' (map maxLabelWidth b)
  _ -> 0

maximum' :: [Int] -> Int
maximum' [] = 0
maximum' a = maximum a
-}
