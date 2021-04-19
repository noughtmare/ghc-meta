module Main where

import GHC.Meta

main :: IO ()
main = print (parseExp "1 + 1")
