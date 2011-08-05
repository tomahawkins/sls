module SLS
  ( Name
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

type Name = String

data Instance a
  = PMOS a a a  -- gate, source, drain
  | NMOS a a a  -- gate, source, drain
  | OUT  Name a
  deriving Show

data Netlist = Netlist [Name] [Instance Name]  -- inputs, instances.

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
netlist name (Netlist ins instances) = unlines
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
  outs = sort [ name | OUT name _ <- instances ]
  nets a = case a of
    PMOS a b c -> [a, b, c]
    NMOS a b c -> [a, b, c]
    OUT  _ a   -> [a]

  instantiate a = case a of
    PMOS gate source drain -> printf "pmos (%s, %s, %s);" drain source gate
    NMOS gate source drain -> printf "nmos (%s, %s, %s);" drain source gate
    OUT  name net          -> printf "buf  (%s, %s);" name net

-- | Each row is output name and value, and a list of input names and values.
type TruthTable = [TruthTableRow]
type TruthTableRow  = (Name, Bool, [(Name, Bool)])

-- | Synthesis given the number of transistors, a number of available internal nets, and the logic function.
synthesize :: Int -> Int -> Int -> TruthTable -> IO (Maybe Netlist)
synthesize pCount nCount netCountInternal truthTable = do
  mapM_ print configurations
  print $ length configurations
  return $ Just $ configNetlist inputs $ head configurations
  where

  -- vdd : gnd : inputs ++ misc nets
  netCountTotal = netCountInternal + 2 + length inputs

  -- Order p_0_gate, p_0_source, p_0_drain
  configurations :: [[Instance Int]]
  configurations = filter (drc $ length inputs) permutations
    where
    pmosPermutations   = [ PMOS gate source drain | [gate, source, drain] <- sequence [all, all, all] ]
    nmosPermutations   = [ NMOS gate source drain | [gate, source, drain] <- sequence [all, all, all] ]
    permutations       = sequence $ replicate pCount pmosPermutations ++ replicate nCount nmosPermutations ++ [ [ OUT name net | net <- all ]  | name <- outputs ]
    all = [0 .. netCountTotal - 1]

  inputs  = sort $ nub $ concat [ fst $ unzip a | (_, _, a) <- truthTable ]
  outputs = sort $ nub [ name | (name, _, _) <- truthTable ]

{-
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
-}

vdd = 0
gnd = 1

drc :: Int -> [Instance Int] -> Bool
drc inputs instances = all drainsNotConnectedToInputsOrPower instances
                    && all sourcesNotConnectedToInputs       instances
                    && all sourcesNotConnectedToWrongSupply  instances
                    && all noPinToPin                        instances
  where
  drainsNotConnectedToInputsOrPower a = case a of
    PMOS _ _ drain -> drain >= inputs + 2
    NMOS _ _ drain -> drain >= inputs + 2
    _ -> True
  sourcesNotConnectedToInputs a = case a of
    PMOS _ source _ -> source < 2 || source >= inputs + 2
    NMOS _ source _ -> source < 2 || source >= inputs + 2
    _ -> True
  sourcesNotConnectedToWrongSupply a = case a of
    PMOS _ source _ -> source /= gnd
    NMOS _ source _ -> source /= vdd
    _ -> True
  noPinToPin a = case a of
    PMOS gate source drain -> gate /= source && source /= drain && gate /= drain
    NMOS gate source drain -> gate /= source && source /= drain && gate /= drain
    _ -> True


configNetlist :: [Name] -> [Instance Int] -> Netlist
configNetlist inputs instances = Netlist inputs $ pmos ++ nmos ++ buf
  where
  pmos = [ PMOS (f g) (f s) (f d)  | PMOS g s d   <- instances ]
  nmos = [ NMOS (f g) (f s) (f d)  | NMOS g s d   <- instances ]
  buf  = [ OUT  name  (f n)        | OUT name n <- instances ]

  f :: Int -> Name
  f net = case net of
    0 -> "vdd"
    1 -> "gnd"
    n | n - 2 < length inputs -> inputs !! (n - 2)
      | otherwise -> printf "net_%d" (n - 2 - length inputs)

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

