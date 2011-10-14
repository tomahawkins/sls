-- | Netlist types and generation.
module SLS.Netlist
  ( Name
  , Net      (..)
  , Instance (..)
  , Netlist  (..)
  , verilog
  , empty
  , nets
  , internalNets
  , inputs
  , outputs
  , pGates
  , nGates
  , pSources
  , nSources
  , pDrains
  , nDrains
  , drains
  ) where

import Data.List
import Text.Printf

type Name = String

data Net
  = Net Int
  | Input Name
  | VDD
  | GND
  deriving Eq

data Instance
  = PMOS Net Net Net -- gate, source, drain
  | NMOS Net Net Net -- gate, source, drain
  | Output Name  Net
  deriving Eq

data Netlist = Netlist Int [Instance] deriving Eq

-- | An empty netlist.
empty :: Netlist
empty = Netlist 0 []

-- | Output a Verilog switch level netlist.
verilog :: Name -> Netlist -> String
verilog name netlist@(Netlist _ instances) = unlines
  [ "module " ++ name
  , "( input  vdd"
  , ", input  gnd"
  , unlines [ ", input  " ++ name | name <- inputs netlist ] ++ unlines [ ", output " ++ name | name <- outputs netlist ] ++ ");"
  , ""
  , unlines [ printf "wire %s;" $ net a | a <- internalNets netlist ]
  , unlines $ map instantiate instances
  , "endmodule"
  ]
  where
  instantiate a = case a of
    PMOS gate source drain -> printf "pmos (%s, %s, %s);" (net drain) (net source) (net gate)
    NMOS gate source drain -> printf "nmos (%s, %s, %s);" (net drain) (net source) (net gate)
    Output name a          -> printf "buf  (%s, %s);" name (net a)

  net a = case a of
    Net a -> case lookup a nets of
      Nothing -> error "net not found"
      Just a  -> a
    Input name -> name
    VDD        -> "vdd"
    GND        -> "gnd"
    where
    nets = [ (i, printf "net%d" i) | Net i <- internalNets netlist ]
    
-- | All nets in a netlist.
nets :: Netlist -> [Net]
nets (Netlist _ instances) = nub $ concatMap nets instances
  where
  nets a = case a of
    PMOS a b c -> [a, b, c]
    NMOS a b c -> [a, b, c]
    Output _ a -> [a]

-- | All internal nets in a netlist.
internalNets :: Netlist -> [Net]
internalNets netlist = [ Net a | Net a <- nets netlist ]

-- | All inputs in a netlist.
inputs :: Netlist -> [Name]
inputs netlist = sort [ name | Input name <- nets netlist ]

-- | All outputs in a netlist.
outputs :: Netlist -> [Name]
outputs (Netlist _ instances) = sort [ name | Output name _ <- instances ]

pGates :: Netlist -> [Net]
pGates (Netlist _ instances ) = [ a | PMOS a _ _ <- instances ]

nGates :: Netlist -> [Net]
nGates (Netlist _ instances ) = [ a | NMOS a _ _ <- instances ]

pSources :: Netlist -> [Net]
pSources (Netlist _ instances ) = [ a | PMOS _ a _ <- instances ]

nSources :: Netlist -> [Net]
nSources (Netlist _ instances ) = [ a | NMOS _ a _ <- instances ]

pDrains :: Netlist -> [Net]
pDrains (Netlist _ instances ) = [ a | PMOS _ _ a <- instances ]

nDrains :: Netlist -> [Net]
nDrains (Netlist _ instances ) = [ a | NMOS _ _ a <- instances ]

drains :: Netlist -> [Net]
drains netlist = pDrains netlist ++ nDrains netlist
