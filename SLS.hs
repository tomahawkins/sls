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
  a <- synthesize 1 1 5
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
synthesize pCount nCount netCount truthTable = do
    writeFile "test.yices" $ unlines $ map show $ smt ++ [CHECK]
    a <- quickCheckY "yices" [] smt
    case a of
      Sat a -> do
        writeFile "result.yices" $ unlines $ map show a
        return $ Just $ configNetlist pCount nCount inputs outputs a
      a -> print a >> return Nothing
  where

  smt :: [CmdY]
  smt = concatMap pinConfig pinConfigs ++ designRules pCount nCount inputs ++ netValueCombinations ++ netValueConstraints

  pinConfig :: Name -> [CmdY]
  pinConfig name = [intVar name, ASSERT $ AND [VarE name :>= LitI 0, VarE name :< LitI (fromIntegral netCount)]]

  inputs  = sort $ nub $ concat [ fst $ unzip a | (_, _, a) <- truthTable ]
  outputs = sort $ nub [ name | (name, _, _) <- truthTable ]

  -- | SMT vars for each pin configuration, i.e. which net it is connected to.
  pinConfigs :: [Name]
  pinConfigs = ["vdd", "gnd"]
      ++ inputs ++ outputs
      ++ concat [ transistorPins $ printf "pmos_%d" i | i <- [0 .. pCount - 1] ]
      ++ concat [ transistorPins $ printf "nmos_%d" i | i <- [0 .. nCount - 1] ]

  transistorPins :: Name -> [Name]
  transistorPins name = [ printf "%s_%s" name pin | pin <- ["gate", "source", "drain"] ]

  -- All possible net value combinations.
  netValues :: [(Int, [Bool])]
  netValues = zip [0 ..] $ sequence $ replicate netCount [False, True]

  -- XXX Only enumerate valid truth table values.  Not everything.  But you don't know the net configuration.  ???
  -- XXX Make vdd, gnd, and inputs hard coded to the the first nets.  Then only valid input sequences would need to be checked.

  -- Net values bound to pins.
  netValueCombinations :: [CmdY]
  netValueCombinations = concatMap f netValues
    where
    f :: (Int, [Bool]) -> [CmdY]
    f (comb, netValues) = concatMap pinValue pinConfigs
      where
      -- Bind pin value to net value.
      pinValue :: Name -> [CmdY]
      pinValue pinConfig = boolVar pinValue : [ ASSERT $ (VarE pinConfig := LitI net) :=> (VarE pinValue := LitB netValue) | (net, netValue) <- zip [0 ..] netValues ]
        where
        pinValue = printf "%s_%d" pinConfig comb

  -- Constraints on net values.
  netValueConstraints :: [CmdY]
  netValueConstraints = concatMap f netValues
    where
    f :: (Int, [Bool]) -> [CmdY]
    f (comb, _) = power ++ io
      where
      value :: String -> ExpY
      value config = VarE $ printf "%s_%d" config comb
      power    = [ASSERT $ value "vdd", ASSERT $ NOT $ value "gnd"]
      pmos     = [ NOT (value $ printf "pmos_%d_gate" i) :=> (value (printf "pmos_%d_source" i) := value (printf "pmos_%d_drain" i)) | i <- [0 .. pCount - 1] ]
      nmos     = [     (value $ printf "nmos_%d_gate" i) :=> (value (printf "nmos_%d_source" i) := value (printf "nmos_%d_drain" i)) | i <- [0 .. nCount - 1] ]
      io       = [ ASSERT $ AND [ value input := LitB val | (input, val) <- inputs ] :=> AND (pmos ++ nmos ++ [value output := LitB val]) | (output, val, inputs) <- truthTable ]

-- Connectivity design rules.
designRules :: Int -> Int -> [Name] -> [CmdY]
designRules pCount nCount inputs' = inputsNotConnectedToVDD
                                 ++ inputsNotConnectedToGND
                                 ++ inputsNotConnectedToDrains
                                 ++ inputsNotConnectedToSources
                                 ++ inputsNotConnectedToOtherInputs
                                 ++ drainsNotConnectedToVDD
                                 ++ drainsNotConnectedToGND
                                 ++ pSourcesNotConnectedToGND
                                 ++ nSourcesNotConnectedToVDD
  where
  vdd = VarE "vdd"
  gnd = VarE "gnd"
  inputs   = map VarE inputs'
  pDrains  = [ VarE $ printf "pmos_%d_drain"  i | i <- [0 .. pCount - 1] ]
  pSources = [ VarE $ printf "pmos_%d_source" i | i <- [0 .. pCount - 1] ]
  nDrains  = [ VarE $ printf "nmos_%d_drain"  i | i <- [0 .. nCount - 1] ]
  nSources = [ VarE $ printf "nmos_%d_source" i | i <- [0 .. nCount - 1] ]
  inputsNotConnectedToVDD = [ ASSERT $ vdd :/= input | input <- inputs ]
  inputsNotConnectedToGND = [ ASSERT $ gnd :/= input | input <- inputs ]
  inputsNotConnectedToDrains  = [ ASSERT $ input :/= drain  | input <- inputs, drain  <- pDrains  ++ nDrains  ]
  inputsNotConnectedToSources = [ ASSERT $ input :/= source | input <- inputs, source <- pSources ++ nSources ]
  inputsNotConnectedToOtherInputs = [ ASSERT $ VarE a :/= VarE b | a <- inputs', b <- inputs', a /= b ]
  drainsNotConnectedToVDD = [ ASSERT $ vdd :/= drain | drain <- pDrains ++ nDrains ]
  drainsNotConnectedToGND = [ ASSERT $ gnd :/= drain | drain <- pDrains ++ nDrains ]
  pSourcesNotConnectedToGND = [ ASSERT $ gnd :/= source | source <- pSources ]
  nSourcesNotConnectedToVDD = [ ASSERT $ vdd :/= source | source <- nSources ]


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

intVar :: Name -> CmdY
intVar name = DEFINE (name, VarT "int") Nothing


{-
CMOS design rules.

- Inputs can only connect to gates and outputs.
- Inputs never tied to other inputs.
- PMOS sources can only connect to PMOS A net with a connecting gate

- Single connected nets (floating pin) or vdd or gnd connected to a gate is sign further reduction can be obtained.
-}

