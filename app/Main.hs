

{-# LANGUAGE  AllowAmbiguousTypes,  TypeApplications, PartialTypeSignatures, NoMonomorphismRestriction,  FlexibleContexts, NoImplicitPrelude
#-}
-- NoMonomorphismRestriction,
module Main where

import Lib
import CCC
import Cat
import Control.Category
import Prelude hiding ((.), id)
import Rewrite
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
-- fails. appears to be another inocherent hiccup. ($) is weird anyway
-- example18 = toCCC @FreeCat ($)

example18 = toCCC @FreeCat f  where f = \g x -> g x
example19 = toCCC @FreeCat (\(g, x) -> g x)

-- fails confusingly. This might mean something is fundmanetally wrong somehwere.
-- example20 = toCCC @FreeCat f  where f = (\x -> (x, \y -> x))
--helper = (\x -> (x, \y -> x))
--example20 = toCCC @FreeCat helper

-- can't tell if this one is correct. It is too big. revisit when I have optimizations
example21 = toCCC @FreeCat f  where f = \h g x -> h g x


-- you can throw catagorocial literals in there if you want
example22 = toCCC @FreeCat (\x -> Id . x)
example23 = toCCC @FreeCat (\(x,y) -> Dup . x)
-- could define helper functions with preapplied (.). dup = (.) Dup 
-- then (\x -> dup x) looks more nautral
example24 = toCCC @FreeCat (\(x,y) -> dup x) where dup = (.) Dup 


example25 = toCCC @FreeCat (\(x,y) -> (x,y))
example26 = toCCC @FreeCat (\(x,(y,z)) -> (y,z))
-- or perhaps  f $$ x = applyC . (fanC f x). This makes sense in that f and x are extractors.
-- And then. 
-- \x -> mysquare x.

-- this all may be just asking to get confused.



-- we could also compile FreeCat as a seperate language, then dump the output to a file and recompile with ghc. Pretty goofy workflow.
-- we can also perhaps find a way to push to an external solver. That would be prettty cool.

-- We could super optimize functions if we have a cetagory equivalence test. Just enumerate all possible functions and find the bets one that matches.
-- Z3?
-- There might be

-- Other possible heurisitcs:
-- Simulated Annealing Maybe.


-- GLobal optimization:
-- Dynamic Programming?
-- MIP ?
-- CSP ?


