

{-# LANGUAGE  AllowAmbiguousTypes,  TypeApplications, PartialTypeSignatures, NoMonomorphismRestriction,  FlexibleContexts
#-}
-- NoMonomorphismRestriction,
module Main where

import Lib
import CCC
import Cat
main :: IO ()
main = someFunc

example2 = toCCC @FreeCat (\(x,y)->(y,x))

-- You need to give the type sginature unfortunately. k is too ambiguous otherwise
-- example3 :: Cartesian k => k _ _
example3 = toCCC (\(z,y)->(z,z))

example4 = toCCC @FreeCat (\((x,y),z) -> x)

example5 = toCCC @FreeCat (\(x,y) -> x + y)

example6 = toCCC @FreeCat (\(x,y) -> y + (x * y))

-- example7 :: Cartesian k => k _ _
example7 = toCCC (\(x,(y,z)) -> (x,(y,z)))

myconst = \x -> \y -> x
example8 = toCCC @FreeCat  myconst -- const -- (\x -> \y -> x)
example9 =  let f = (\x y -> x) in toCCC @FreeCat f
example10 =  toCCC @FreeCat (\x -> x)
example11 =  toCCC @FreeCat f where f = (\x y -> y)

-- raw const is failing, but when you give it a name it doesn't. Very alarming.
-- This is almost certainly because of something in the Incoherent 


--example12 :: Cartesian k => k (k a b) b  
example12 =  toCCC @FreeCat ((\x y -> y) :: a -> b -> b)

-- the following incorrectly fails. Early picking of incoherentinstamce seems to send it into case 3 of CCC rather than curry case 2.
-- This isn't producing incorrect code, but it does suck.
-- doesnotwork =  toCCC @FreeCat (\x y -> y) 

-- Even this is fine
-- example16 =  toCCC @FreeCat ((\x y -> y) :: _ -> _ -> _)
example13 = toCCC @FreeCat (\x y -> (x,y))
example14 = toCCC @FreeCat f where f = (\x y z -> z)
example15 = toCCC @FreeCat f where f = (\x y z -> x)

--example13 = toCCC (\(x,y) -> y)
example1 = toCCC @FreeCat id

example16 = toCCC @FreeCat (+)

example17 = toCCC @FreeCat (*)
