module Main where

import SLS
import SLS.Choice

main :: IO ()
main = do
  print $ length ns
  mapM_ (putStrLn . verilog "blah") ns

ns = f $ f $ initialChoices ["a"] ["x"]

f = concatMap $ nextChoices ["a"]

