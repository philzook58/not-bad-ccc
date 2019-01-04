{-# LANGUAGE GADTs,   ImpredicativeTypes,   RankNTypes,  NoImplicitPrelude #-}
module Rewrite where

import Cat
import Control.Category
import Prelude hiding ((.), id)
-- a dead dumb simple rewrite system
-- it is expecially easy since our ctagoerical lnauggae has no names in it

-- even if I get GHC rewrite rules to work. this will be useful for comparison.
-- with a test suite for example. Would give us clues as to which rewrite rules are not firing.


-- we can just abuse haskell pattern matching to do most of the work for us


-- we should move the definition of FreeCat here.
-- Add a literal constructor 
-- Lit :: k a b -> FreeCat a b... No this hides k....
-- well, we'l;l figure out that problem later


-- Maybe we want to check out that TTT tool.
-- dev.stephendiehl.com/rewrite.pdf

-- Either (FreeCat a b) (FreeCat a b) -- return original argyument if fails?

type Rule = forall a b. FreeCat a b -> Maybe (FreeCat a b)
-- stop using prefix rule. It is annoying
rule_paren :: Rule -- FreeCat a b -> Maybe (FreeCat a b)
rule_paren (Comp (Comp f g) h) = Just (Comp f (Comp g h))
rule_paren _ = Nothing

rule_fstsndpar :: FreeCat a b -> Maybe (FreeCat a b)
rule_fstsndpar (Comp (Par Fst Snd) Dup) = Just Id
rule_fstsndpar _ = Nothing

rule_fst_dup :: FreeCat a b -> Maybe (FreeCat a b)
rule_fst_dup (Comp Fst Dup) = Just Id
rule_fst_dup _ = Nothing

rule_snd_dup :: FreeCat a b -> Maybe (FreeCat a b)
rule_snd_dup (Comp Snd Dup) = Just Id
rule_snd_dup _ = Nothing

rule_par_dup :: FreeCat a b -> Maybe (FreeCat a b)
rule_par_dup (Comp (Par (Comp f Fst) (Comp g Snd)) Dup) = Just (Par f g)
rule_par_dup _ = Nothing

rule_par_dup' :: FreeCat a b -> Maybe (FreeCat a b)
rule_par_dup' (Comp (Par (Comp f Fst) (Comp g Fst)) Dup) = Just (((Par f g) . Dup) . Fst)
rule_par_dup' _ = Nothing

rule_par_dup'' :: FreeCat a b -> Maybe (FreeCat a b)
rule_par_dup'' (Comp (Par (Comp f Snd) (Comp g Snd)) Dup) = Just (((Par f g) . Dup) . Snd)
rule_par_dup'' _ = Nothing

-- parC dupC" forall f. (_parC f f) . _dupC = _dupC . f
{- -- needs equality.
rule_par_dup_eq :: FreeCat a b -> Maybe (FreeCat a b)
rule_par_dup_eq (Comp (Par f f) Dup) | f == f = Dup . f
-}


-- build the curry rules.



rule_id_left :: FreeCat a b -> Maybe (FreeCat a b)
rule_id_left (Comp Id f) = Just f
rule_id_left _ = Nothing 

rule_id_right :: FreeCat a b -> Maybe (FreeCat a b)
rule_id_right (Comp f Id) = Just f
rule_id_right _ = Nothing

allRules :: [Rule]
allRules = [rule_fstsndpar, rule_id_right, rule_id_left, rule_fst_dup, rule_snd_dup, rule_par_dup, rule_par_dup', rule_par_dup''] -- rule-paren
-- turned off rule_paren because it actually hurts the ability to compress the nasty fanout behavior.

-- yeah. Easily possible to get nasty infinite loops
recurseMatch :: Rule -> FreeCat a b -> Maybe (FreeCat a b)
recurseMatch rule x = case rule x of
                             Nothing -> goDown (recurseMatch rule) x -- This rule didn't match. Try going down and matching there.
                             Just x' -> Just x' -- travFree rule x' -- or can keep trying while we're already there.


goDown :: Rule -> FreeCat a b -> Maybe (FreeCat a b)
goDown z (Comp f g) = case (z f) of
                               Nothing -> case (z g) of
                               	               Nothing -> Nothing
                               	               Just x -> Just (Comp f x)
                               Just x -> Just (Comp x g) 
goDown z (Par f g) = case (z f) of
                               Nothing -> case (z g) of
                               	               Nothing -> Nothing -- nothing in either subtree macthed
                               	               Just x -> Just (Par f x) -- 
                               Just x -> Just (Par x g)  -- something in f matched the rule
goDown _ _ = Nothing -- can't go down
{-
goDown z (Par f g) = Par (z f) (z g)
goDown z Dup = Dup
goDown _ Fst = Fst
goDown _ Snd = Snd
goDown _ f = f
-}

{-
travFree rule x@(Comp f g) = case rule x of
                             Nothing -> Comp (travFree rule f) (travFree rule g)
                             Just x' -> travFree rule x'
travFree rule Id = case rule Id of
	                  Nothing -> Id
	                  Just x' -> travFree rule x'
-}
-- can recursively go down rules until onew hits, then start all over. Put common rules first.

type Rule' a b = FreeCat a b -> Maybe (FreeCat a b)

rewrite' :: [Rule] -> [Rule] -> FreeCat a b -> FreeCat a b
rewrite' _ [] k = k -- no rules matched 
rewrite' allrules (rule : rules) k = case recurseMatch rule k of
                                       Nothing -> rewrite' allrules rules k -- try the next rule
                                       Just k' -> rewrite' allrules allrules k' -- start over from the beginning

rewrite rules k = rewrite' rules rules k
simplify k = rewrite allRules k





