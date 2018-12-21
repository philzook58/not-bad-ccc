

{-# LANGUAGE    TypeApplications, PartialTypeSignatures
#-}

module Main where

import Lib
import CCC
import Cat
main :: IO ()
main = someFunc

example2 = toCCC @FreeCat (\(x,y)->(y,x))

-- You need to give the type sginature unfortunately. k is too ambiguous otherwise
example3 :: Cartesian k => k _ _
example3 = toCCC (\(z,y)->(z,z))

example4 = toCCC @FreeCat (\((x,y),z) -> x)

example5 = toCCC @FreeCat (\(x,y) -> x + y)

example6 = toCCC @FreeCat (\(x,y) -> y + (x * y))

example7 :: Cartesian k => k _ _
example7 = toCCC (\(x,(y,z)) -> (x,(y,z)))


