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
  a <- synthesize 2 3 4
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
  , unlines [ "wire " ++ name | name <- nub (concatMap nets instances) \\ (["vdd", "gnd"] ++ ins ++ outs) ]
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
    print a
    case a of
      Sat a -> return $ Just $ configNetlist pCount nCount inputs outputs a
      a -> print a >> return Nothing
  where

  smt :: [CmdY]
  smt = concatMap pinConfig pinConfigs ++ netValueCombinations ++ netValueConstraints

  pinConfig :: Name -> [CmdY]
  pinConfig name = [intVar name, ASSERT $ AND [VarE name :>= LitI 0, VarE name :< LitI (fromIntegral netCount)]]

  inputs  = sort $ nub $ concat [ fst $ unzip a | (_, _, a) <- truthTable ]
  outputs = sort $ nub [ name | (name, _, _) <- truthTable ]

  -- | SMT vars for each pin configuration, i.e. which net it is connected to.
  pinConfigs :: [Name]
  pinConfigs = ["vdd", "gnd"]
      ++ inputs ++ outputs
      ++ concat [ transistorPins $ printf "pmos_%d" i | i <- [0.. pCount] ]
      ++ concat [ transistorPins $ printf "nmos_%d" i | i <- [0.. nCount] ]

  transistorPins :: Name -> [Name]
  transistorPins name = [ printf "%s_%s" name pin | pin <- ["gate", "source", "drain"] ]

  -- All possible net value combinations.
  netValues :: [(Int, [Bool])]
  netValues = zip [0 ..] $ sequence $ replicate netCount [False, True]

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
  netValueConstraints = [ASSERT $ OR $ map f netValues]
    where
    f :: (Int, [Bool]) -> ExpY
    f (comb, netValues) = power
      where
      power = AND [VarE $ printf "vdd_%d" comb, NOT $ VarE $ printf "gnd_%d" comb]
      


configNetlist :: Int -> Int -> [Name] -> [Name] -> [ExpY] -> Netlist
configNetlist pCount nCount inputs outputs result = Netlist inputs outputs $ pmos ++ nmos ++ buf
  where
  pmos = [ PMOS (f $ printf "pmos_%d_gate" i) (f $ printf "pmos_%d_source" i) (f $ printf "pmos_%d_drain" i) | i <- [0 .. pCount] ]
  nmos = [ NMOS (f $ printf "nmos_%d_gate" i) (f $ printf "nmos_%d_source" i) (f $ printf "nmos_%d_drain" i) | i <- [0 .. nCount] ]
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

{-
truthTableRow :: Int -> Int -> Int -> (Int, TruthTableRow) -> [CmdY]
truthTableRow pCount nCount netCount (row, (outputName, outputValue, inputs)) = map boolVar nets ++ inputValues ++ outputValues
  where
  nets :: [Name]
  nets = [ printf "net_%d_%d" net row | net <- [0 .. netCount - 1] ]
  inputValues  = [ ASSERT $ (VarE inputName  := LitI (fromIntegral net)) :=> (VarE (printf "net_%d_%d" net row) := LitB inputValue ) | (inputName, inputValue) <- inputs, net <- [0 .. netCount - 1] ]
  outputValues = [ ASSERT $ (VarE outputName := LitI (fromIntegral net)) :=> (VarE (printf "net_%d_%d" net row) := LitB outputValue) | net <- [0 .. netCount - 1] ]

  pmosValues = concat
    [ [ boolVar gate
      , boolVar source
      , boolVar drain
      , ASSERT $ (VarE gate' := Lit (fromIntegral net)) :=> (VarE gate := VarE (printf "net_%d_%d" net row))  -- XXX This is not going to work.  What happens when a pin is floating?  SMT will pick a value to make it meet the spec.  Need to handle 4-state logic (10xz).
      ]
    | trans <- [0 .. pCount - 1]
    , let gate'   = printf "pmos_%d_gate"   trans
          source' = printf "pmos_%d_source" trans
          drain'  = printf "pmos_%d_drain"  trans
          gate    = printf "%s_%d" gate'   row
          source  = printf "%s_%d" source' row
          drain   = printf "%s_%d" drain'  row
    , net <- [0 .. netCount - 1]
    ]

    ASSERT $ (VarE outputName := LitI (fromIntegral net)) :=> (VarE (printf "net_%d_%d" net row) := LitB outputValue) | net <- [0 .. netCount - 1] ]
-}

boolVar :: Name -> CmdY
boolVar name = DEFINE (name, VarT "bool") Nothing

intVar :: Name -> CmdY
intVar name = DEFINE (name, VarT "int") Nothing


{-
CMOS design rules.

- Each net has >= 2 connecting pins.
- Inputs can only connect to gates and outputs.
- Inputs never tied to other inputs.
- PMOS sources can only connect to PMOS A net with a connecting gate
-
...
-}

