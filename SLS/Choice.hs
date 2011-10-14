module SLS.Choice
  ( initialChoices
  , nextChoices
  ) where

import Data.List

import SLS.Netlist

-- | A list of starting netlists.
initialChoices :: [Name] -> [Name] -> [Netlist]
initialChoices inputs outputs = f outputs empty
  where
  f :: [Name] -> Netlist -> [Netlist]
  f [] a = [a]
  f (output : outputs) (Netlist next instances) = concatMap (f outputs) $
    [ Netlist next (Output output VDD : instances)
    , Netlist next (Output output GND : instances)
    , Netlist (next + 1) (Output output (Net next) : instances)
    ] ++ [ Netlist next (Output output (Input input) : instances) | input <- inputs ]

-- | Given a list of inputs and a partially constructed netlist, returns a new list of further constructed netlists.  Assumes outputs are included.
nextChoices :: [Name] -> Netlist -> [Netlist]
nextChoices inputs netlist@(Netlist next instances) = addPMOS ++ addNMOS ++ connectOutput
  where
  addPMOS = [ Netlist (next + 2) (PMOS (Net next) source (Net $ next + 1) : instances) | source <- VDD : pDrains netlist ]
  addNMOS = [ Netlist (next + 2) (NMOS (Net next) source (Net $ next + 1) : instances) | source <- GND : nDrains netlist ]
  connectOutput = [ Netlist next $ Output name drain : delete output instances | output@(Output name net@(Net _)) <- instances, notElem net $ drains netlist, drain <- drains netlist ]

{-
-- | Synthesis given the number of transistors, a number of available internal nets, and the logic function.
synthesize :: Int -> Int -> Int -> TruthTable -> IO (Maybe Netlist)
synthesize pCount nCount netCountInternal truthTable = do
  print $ length configurations
  --verified $ zip [0 ..] configurations
  return Nothing
  where

  -- vdd : gnd : inputs ++ misc nets
  netCountTotal = netCountInternal + 2 + length inputs

  verified :: [(Int, [Instance Int])] -> IO (Maybe Netlist)
  verified [] = return Nothing
  verified ((n, a) : b) = do
    writeFile (printf "netlist%d.v" n) $ verilog "inverter" $ configNetlist inputs a
    r <- verify netCountTotal inputs truthTable (n, a)
    if False --r
      then return $ Just $ configNetlist inputs a
      else putStrLn "failed to verify" >> verified b

  -- Order p_0_gate, p_0_source, p_0_drain
  configurations :: [[Instance Int]]
  configurations = filter (drc (length inputs) netCountTotal) permutations
    where
    pmosPermutations   = [ PMOS gate source drain | [gate, source, drain] <- sequence [all, all, all] ]
    nmosPermutations   = [ NMOS gate source drain | [gate, source, drain] <- sequence [all, all, all] ]
    permutations       = sequence $ replicate pCount pmosPermutations ++ replicate nCount nmosPermutations ++ [ [ OUT name net | net <- all ]  | name <- outputs ]
    all = [0 .. netCountTotal - 1]

  inputs  = sort $ nub $ concat [ fst $ unzip a | (_, _, a) <- truthTable ]
  outputs = sort $ nub [ name | (name, _, _) <- truthTable ]

vdd = 0
gnd = 1

drc :: Int -> Int -> [Instance Int] -> Bool
drc inputs totalNets instances = all drainsNotConnectedToInputsOrPower instances
                              && all sourcesNotConnectedToInputs       instances
                              && all sourcesNotConnectedToWrongSupply  instances
                              && all noPinToPin                        instances
			      && all internalNetHasValidDriver         internalNets
			      && all noPDrainToNSource                 internalNets
			      && all noNDrainToPSource                 internalNets
  where
  internalNets = [2 + inputs .. totalNets - 1]

  anyPGate net = not $ null [ () | PMOS gate _ _ <- instances, gate == net ]
  anyNGate net = not $ null [ () | NMOS gate _ _ <- instances, gate == net ]
  anyGate  net = anyPGate net || anyNGate net

  anyPSource net = not $ null [ () | PMOS _ source _ <- instances, source == net ]
  anyNSource net = not $ null [ () | NMOS _ source _ <- instances, source == net ]
  anySource  net = anyPSource net || anyNSource net

  anyPDrain net = not $ null [ () | PMOS _ _ drain <- instances, drain == net ]
  anyNDrain net = not $ null [ () | NMOS _ _ drain <- instances, drain == net ]
  anyDrain  net = anyPDrain net || anyNDrain net

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

  internalNetHasValidDriver :: Int -> Bool
  internalNetHasValidDriver net = anyDrain net

  noPDrainToNSource :: Int -> Bool
  noPDrainToNSource net = not $ anyPDrain net && anyNSource net

  noNDrainToPSource :: Int -> Bool
  noNDrainToPSource net = not $ anyNDrain net && anyPSource net

  noGateDrainLoops :: Bool
  noGateDrainLoops = True

  noDrainSourceLoops :: Bool
  noDrainSourceLoops = True


verify :: Int -> [Name] -> TruthTable -> (Int, [Instance Int]) -> IO Bool
verify totalNets inputs truthTable (n, instances) = do
  writeFile (printf "config%d.yices" n) $ unlines $ map show $ smt ++ [CHECK]
  r <- quickCheckY "yices" [] smt
  case r of
    UnSat _ -> return True
    _ -> return False
  where
  f :: Int -> ExpY
  f a = VarE $ printf "n%d" a
  smt = [ boolVar $ printf "n%d" net | net <- [0 .. totalNets - 1] ] ++ [ASSERT $ f 0 := LitB True, ASSERT $ f 1 := LitB False] ++ [ASSERT $ NOT $ AND (power ++ pmos ++ nmos) :=> AND table]
  power = [f 0 := LitB True, f 1 := LitB False]
  pmos  = [ NOT (f gate) :=> (f source := f drain) | PMOS gate source drain <- instances ]
  nmos  = [     (f gate) :=> (f source := f drain) | NMOS gate source drain <- instances ]
  table = [ AND [ inputNet inputName := LitB inputValue | (inputName, inputValue) <- inputs ] :=> (outputNet outputName := LitB outputValue) | (outputName, outputValue, inputs) <- truthTable ]

  outputNet :: Name -> ExpY
  outputNet name = f $ head [ net | OUT name' net <- instances ]

  inputNet :: Name -> ExpY
  inputNet name = f (2 + (fromJust $ elemIndex name inputs))


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
-}
