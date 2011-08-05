module SLS
  ( Net
  , Name
  , Instance (..)
  , Netlist  (..)
  , synthesize
  , netlist
  , example
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
  | BUF  Net Net      -- input, output

data Netlist = Netlist [Net] [Net] [Instance]  -- inputs, outputs, instance

-- | Synthesis example.
example :: IO ()
example = do
  a <- synthesize 1 1 1
    [ ("x", True , [("a", False)])
    , ("x", False, [("a", True )])
    ]
  case a of
    Nothing -> putStrLn "Synthesis failed."
    Just a  -> putStrLn $ netlist "inverter" a

-- | Output a Verilog switch level netlist.
netlist :: Name -> Netlist -> String
netlist name (Netlist ins outs instances) = unlines
  [ "module " ++ name
  , "\t( input  vdd"
  , "\t, input  gnd"
  , unlines [ "\t, input  " ++ name | name <- ins ] ++ unlines [ "\t, output " ++ name | name <- outs ] ++ "\t);"
  , ""
  , unlines [ printf "wire %s;" name | name <- nub (concatMap nets instances) \\ (["vdd", "gnd"] ++ ins ++ outs) ]
  , unlines $ map instantiate instances
  , "endmodule"
  ]
  where
  nets a = case a of
    PMOS a b c -> [a, b, c]
    NMOS a b c -> [a, b, c]
    BUF  a b   -> [a, b]

  instantiate a = case a of
    PMOS gate source drain -> printf "pmos (%s, %s, %s);" drain source gate
    NMOS gate source drain -> printf "nmos (%s, %s, %s);" drain source gate
    BUF  input output      -> printf "buf  (%s, %s);" output input

-- | Each row is output name and value, and a list of input names and values.
type TruthTable = [TruthTableRow]
type TruthTableRow  = (Name, Bool, [(Name, Bool)])

-- | Synthesis given the number of transistors, a number of available internal nets, and the logic function.
synthesize :: Int -> Int -> Int -> TruthTable -> IO (Maybe Netlist)
synthesize pCount nCount netCountInternal truthTable = do
    writeFile "test.yices" $ unlines $ map show $ smt ++ [CHECK]
    a <- quickCheckY "yices" [] smt
    case a of
      Sat a -> do
        writeFile "result.yices" $ unlines $ map show a
        return $ Just $ configNetlist pCount nCount inputs outputs a
      a -> print a >> return Nothing
  where

  smt :: [CmdY]
  smt = powerAndInputConstants ++ pinConfigs ++ designRules pCount nCount inputs ++ bindNetValuesToPins ++ pinValueConstraints

  inputs  = sort $ nub $ concat [ fst $ unzip a | (_, _, a) <- truthTable ]
  outputs = sort $ nub [ name | (name, _, _) <- truthTable ]

  -- vdd : gnd : inputs ++ misc nets
  netCountTotal = netCountInternal + 2 + length inputs

  powerAndInputConstants = comment "Power, ground, and input net constants..." ++ concat [ intConst name i | (i, name) <- zip [0 ..] $ ["vdd", "gnd"] ++ inputs ]

  pinConfigNames = outputs ++ concat [ transistorPins $ printf "pmos_%d" i | i <- [0 .. pCount - 1] ] ++ concat [ transistorPins $ printf "nmos_%d" i | i <- [0 .. nCount - 1] ]
    where
    transistorPins :: Name -> [Name]
    transistorPins name = [ printf "%s_%s" name pin | pin <- ["gate", "source", "drain"] ]

  -- | SMT vars for each output and transistor pin configuration, i.e. which net it is connected to.
  pinConfigs :: [CmdY]
  pinConfigs = comment "Pin-to-net connection configurations..." ++ concatMap pinConfig pinConfigNames
    where
    pinConfig :: Name -> [CmdY]
    pinConfig name = [intVar name, ASSERT $ AND [VarE name :>= LitI 0, VarE name :< LitI (fromIntegral netCountTotal)]]

  -- All possible net value combinations, constrained by input values specified in truthTable.
  netValues :: [(Int, [Bool])]
  netValues = zip [0 ..] $ filter inTable $ map ([True, False] ++) $ sequence $ replicate (netCountTotal - 2)  [False, True]
    where
    inTable :: [Bool] -> Bool
    inTable nets = any match truthTable
      where
      inputNets = zip inputs $ take (length inputs) $ drop 2 nets
      match :: TruthTableRow -> Bool
      match (_, _, inputValues) = sort inputValues == sort [ (name, value) | (name, value) <- inputNets, elem name $ fst $ unzip inputValues ]

  bindNetValuesToPins :: [CmdY]
  bindNetValuesToPins = comment "Bind net values to transistor and output pins, define power in input constants..." ++ constants ++ concatMap f netValues
    where
    constants = concat [ concat [ boolConst (printf "%s_%d" name comb) value | (name, value) <- zip (["vdd", "gnd"] ++ inputs) netValues ] | (comb, netValues) <- netValues ]
    f :: (Int, [Bool]) -> [CmdY]
    f (comb, netValues) = concatMap pinValue pinConfigNames
      where
      -- Bind pin value to net value.
      pinValue :: Name -> [CmdY]
      pinValue pinConfig = boolVar pinValue : [ ASSERT $ (VarE pinConfig := LitI net) :=> (VarE pinValue := LitB netValue) | (net, netValue) <- zip [0 ..] netValues ]
        where
        pinValue = printf "%s_%d" pinConfig comb

  -- Constraints on transistor and output pins.
  pinValueConstraints :: [CmdY]
  pinValueConstraints = comment "Pin value constraints..." ++ concatMap f netValues
    where
    f :: (Int, [Bool]) -> [CmdY]
    f (comb, _) = io
      where
      value :: String -> ExpY
      value config = VarE $ printf "%s_%d" config comb
      pmos     = [ NOT (value $ printf "pmos_%d_gate" i) :=> (value (printf "pmos_%d_source" i) := value (printf "pmos_%d_drain" i)) | i <- [0 .. pCount - 1] ]
      nmos     = [     (value $ printf "nmos_%d_gate" i) :=> (value (printf "nmos_%d_source" i) := value (printf "nmos_%d_drain" i)) | i <- [0 .. nCount - 1] ]
      io       = [ ASSERT $ AND (pmos ++ nmos ++ [value output := LitB val]) :=> AND [ value input := LitB val | (input, val) <- inputs ] | (output, val, inputs) <- truthTable ]

-- Connectivity design rules.
designRules :: Int -> Int -> [Name] -> [CmdY]
designRules pCount nCount inputs' = comment "Design rule constraints..."
  ++ inputsNotConnectedToDrains
  ++ inputsNotConnectedToSources
  ++ drainsNotConnectedToVDD
  ++ drainsNotConnectedToGND
  ++ pSourcesNotConnectedToGND
  ++ nSourcesNotConnectedToVDD
  ++ noSelfShorts
  where
  vdd = VarE "vdd"
  gnd = VarE "gnd"
  inputs   = map VarE inputs'
  pGates   = [ VarE $ printf "pmos_%d_gate"   i | i <- [0 .. pCount - 1] ]
  pSources = [ VarE $ printf "pmos_%d_source" i | i <- [0 .. pCount - 1] ]
  pDrains  = [ VarE $ printf "pmos_%d_drain"  i | i <- [0 .. pCount - 1] ]
  nGates   = [ VarE $ printf "nmos_%d_gate"   i | i <- [0 .. nCount - 1] ]
  nSources = [ VarE $ printf "nmos_%d_source" i | i <- [0 .. nCount - 1] ]
  nDrains  = [ VarE $ printf "nmos_%d_drain"  i | i <- [0 .. nCount - 1] ]
  inputsNotConnectedToDrains  = [ ASSERT $ input :/= drain  | input <- inputs, drain  <- pDrains  ++ nDrains  ]
  inputsNotConnectedToSources = [ ASSERT $ input :/= source | input <- inputs, source <- pSources ++ nSources ]
  drainsNotConnectedToVDD = [ ASSERT $ vdd :/= drain | drain <- pDrains ++ nDrains ]
  drainsNotConnectedToGND = [ ASSERT $ gnd :/= drain | drain <- pDrains ++ nDrains ]
  pSourcesNotConnectedToGND = [ ASSERT $ gnd :/= source | source <- pSources ]
  nSourcesNotConnectedToVDD = [ ASSERT $ vdd :/= source | source <- nSources ]
  noSelfShorts = [ ASSERT $ AND [gate :/= source, gate :/= drain, source :/= drain] | (gate, source, drain) <- zip3 (pGates ++ nGates) (pSources ++ nSources) (pDrains ++ nDrains) ]


configNetlist :: Int -> Int -> [Name] -> [Name] -> [ExpY] -> Netlist
configNetlist pCount nCount inputs outputs result = Netlist inputs outputs $ pmos ++ nmos ++ buf
  where
  pmos = [ PMOS (f $ printf "pmos_%d_gate" i) (f $ printf "pmos_%d_source" i) (f $ printf "pmos_%d_drain" i) | i <- [0 .. pCount - 1] ]
  nmos = [ NMOS (f $ printf "nmos_%d_gate" i) (f $ printf "nmos_%d_source" i) (f $ printf "nmos_%d_drain" i) | i <- [0 .. nCount - 1] ]
  buf  = [ BUF (f output) output | output <- outputs, output /= f output ]

  f :: Name -> Name
  f name = case lookup name config of
    Nothing -> error $ "net not found: " ++ name
    Just net -> netName net

  config :: [(Name, Int)]
  config = [ (name, fromIntegral net) | VarE name := LitI net <- result ]

  netName :: Int -> Name
  netName net = case lookup net $ inputNets ++ outputNets of
    Just name -> name
    Nothing   -> printf "net_%d" net
    where
    inputNets  = [ (net, name) | (name, net) <- config, elem name (["vdd", "gnd"] ++ inputs) ]
    outputNets = [ (net, name) | (name, net) <- config, elem name outputs ]

boolVar :: Name -> CmdY
boolVar name = DEFINE (name, VarT "bool") Nothing

boolConst :: Name -> Bool -> [CmdY]
boolConst name value = [boolVar name, ASSERT (VarE name := LitB value)]

intVar :: Name -> CmdY
intVar name = DEFINE (name, VarT "int") Nothing

intConst :: Name -> Int -> [CmdY]
intConst name value = [intVar name, ASSERT (VarE name := LitI (fromIntegral value))]

comment :: String -> [CmdY]
comment _ = [] --[ECHO "", ECHO a]

{-
CMOS design rules.

- Inputs can only connect to gates and outputs.
- Inputs never tied to other inputs.
- PMOS sources can only connect to PMOS A net with a connecting gate

- Single connected nets (floating pin) or vdd or gnd connected to a gate is sign further reduction can be obtained.
-}

