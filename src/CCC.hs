{-# LANGUAGE DataKinds, 
    AllowAmbiguousTypes, 
    TypeFamilies, 
    TypeOperators, 
    MultiParamTypeClasses, 
    FunctionalDependencies, 
    PolyKinds, 
    FlexibleInstances, 
    UndecidableInstances,
    TypeApplications,
    NoImplicitPrelude,
    ScopedTypeVariables,
    FlexibleContexts #-}
module CCC (
     toCCC )where

import Control.Category
import Prelude hiding ((.), id)
import Cat


-- not IsTup anymore. IsArrTup
class IsTup a b | a -> b
instance {-# INCOHERENT #-} (c ~ 'True) => IsTup (a,b) c
instance {-# INCOHERENT #-} (c ~ 'True) => IsTup (a -> b) c
instance {-# INCOHERENT #-} (b ~ 'False) => IsTup a b


-- class IsCurry a b | a -> b
-- instance {-# INCOHERENT #-} (d ~ 'True) => IsCurry (a -> (b -> c)) d
-- instance {-# INCOHERENT #-} (b ~ 'False) => IsCurry a b



class CCC (flag :: Bool) input out | flag input -> out where -- 
    toCCC' :: input -> out

-- toCCC reduces to the case of (stuff) -> single thing that is not -> or (,)
-- curry and fan 
toCCC :: forall k a b a' b' fb. (
          Category k,
          CCC fb (a -> b) (k a' b'),
          IsTup b fb ) => (a -> b) -> k a' b'
toCCC f = toCCC' @fb @(a -> b) @(k a' b') f

instance (Cartesian k,
          IsTup b fb,
          IsTup c fc,
          CCC fb (a -> b) (k a' b'),
          CCC fc (a -> c) (k a' c')) => CCC 'True (a -> (b,c)) (k a' (b', c')) where
    toCCC' f = fanC (toCCC' @fb (fst . f)) (toCCC' @fc (snd . f)) 

-- curry and then uncurry result
instance (Closed k,
          IsTup c fc,
          CCC fc ((a,b)->c)  (k (a',b') c')
          ) => CCC 'True (a -> (b -> c)) (k a' (k b' c')) where
    toCCC' f = curryC (toCCC' @fc (uncurry f)) 

-- base case actually builds the input once the output cannot be detructed more
-- input can be anything, arrow tuple or polymorphic. Output has to be polymorphic
instance (Cartesian k,
          IsTup a fa,
          BuildInput a fa (k a' a'),
          (k a' b') ~ b) => CCC 'False (a -> b) (k a' b') where
    toCCC' f = f input where 
        input = (buildInput @a @fa (idC @k @a'))


{-
instance (Cartesian k,
          IsTup a fa,
          IsTup b fb,
          BuildInput a fa (k a' a'),
          FanOutput fb b (k a' b')) => CCC 'False (a -> b) (k a' b') where
    toCCC' f = fanOutput @fb output where 
        input = (buildInput @a @fa (idC @k @a'))
        output = f input
    
-}




-- does path actuall need to be here? Maybe it does. because we need to be able to extract from it or not
class BuildInput tup (flag :: Bool) path where
    buildInput :: path -> tup
    -- buildInput :: forall k. Cartesian k => k a b -> tup

instance (Cartesian k,
          IsTup a fa,
          IsTup b fb,
          BuildInput a fa (k x a'), 
          BuildInput b fb (k x b'),
          ((k x (a',b')) ~ cat)) =>  BuildInput (a,b) 'True cat where
    buildInput path = (buildInput @a @fa patha, buildInput @b @fb pathb) where
                 patha = fstC . path
                 pathb = sndC . path

instance (Closed k, 
         cat ~ k x (k a' b'), -- cat extract morphisms from input tuple 
         FanOutput fa a cat', 
         cat' ~ k x a', -- ? Is this acceptable?
         cat'' ~ k x b', -- the type of path'
         IsTup b fb,
         IsTup a fa,
         BuildInput b fb cat'') => BuildInput (a -> b) 'True cat where -- toCCC x?
    -- path is location of input morphism in question inside of tuple
    -- x may be a tuple to be deucosturcted
    -- or x may be arrow to be toCCC ed
    buildInput path = \x -> let path' = applyC . (fanC path (fanOutput @fa x)) in buildInput @b @fb path'


instance (Category k, a ~ k a' b') => BuildInput a  'False (k a' b') where
    buildInput path = path

{-
class BuildInputArr (flag :: Bool) arr where
    buildArr :: path -> arr
instance BuildInputArr 'True (a -> b) where -- toCCC x?
    buildArr path = \x -> let path' = applyC . (fanC path (autoUncurry x)) in buildInput @b path'
-}

-- 'a' could be a tuple value, or it could be an arrow value. or a raw morphism
-- seperate type classe instances? for all of them?



-- Does FanOput even need the flag?
-- isn't it all directed now?
-- it doesn't need the incoherent version. A regular overlapping instance.

class FanOutput (flag :: Bool) out cat where -- | out flag -> cat
    fanOutput :: out -> cat

instance (Category k, 
          IsTup b fb,
          CCC fb (a -> b) (k a' b')         
    ) => FanOutput 'True (a -> b) (k a' b') where
    fanOutput f = toCCC' @fb f 

instance (Category k, kab ~ k a b) => FanOutput 'False kab (k a b) where
    fanOutput f = f 

instance (Cartesian k,
         IsTup a fa,
         IsTup b fb,
         FanOutput fa a (k x a'),
         FanOutput fb b (k x b'),
         k x (a', b') ~ cat
         )
          => FanOutput 'True (a, b) cat where
    fanOutput (x,y) = fanC (fanOutput @fa x) (fanOutput @fb y)

{-
class DestructOutput (flag :: Bool) out cat path | out flag path -> cat where
    destructOutput :: path -> out -> cat

instance DesctructOutput 'True (a -> b) cat path where
    destructOutput p f = destructOutput (post . curryC) (sndC . pre)  output where 
        input = buildInput @a @fa (fstC . p)
        output = f input

-}


{-
toCCC :: forall k a b a' b' fa fb x. (IsTup a fa, IsTup b fb, Cartesian k, BuildInput a fa (k a' a'), FanOutput fb b (k a' b')) => (a -> b) -> k a' b'
toCCC f = fanOutput @fb output where
                                      input = buildInput @a @fa (idC @k @a')
                                      output = f input

class AutoUncurry (flag :: Bool) a b | a flag -> b where
    autoUncurry :: a -> b

instance ( IsCurry c f,
           AutoUncurry f ((a,b) -> c) d) => AutoUncurry 'True (a -> (b -> c)) d where
   autoUncurry f = autoUncurry @f (uncurry f) -- postprocess' = curryC . postprocess

instance (a ~ d) => AutoUncurry 'False a d where
   autoUncurry f = f -- Actually recurse into BuildTup and FanOutput here. and then apply post processing
-- autoUncurry post f = post (f buildInput)
-- autoUncurry post f = (post, f) -- to be put together later after fanning
-- toCCC' path post f
-- positive and negative position, do different thing,
-- for positive tuple, fan
-- for positive arrow, uncrry
-- for negative arrow, apply
-- for negative tuple, path
-}
-- (( -> ) -> ) -> .
-- means that the function is going to give us another function, which we'll have to build the input for
-- That's recursive toCCC call? Or partial toCCC without postprocessing.

-- combine BuildInputTup and BuildInputArr into single typeclass
-- think about it in terms of  k a b -> (, , )



-- autoCPS. CPS in the category layer? forall b. k (k a b) b

-- what if output is (a, a -> b)? -> ( a , k a b). I guess we call toCCC on it again? but we need
 {-   (a -> (b -> a)
    curry fstC
    parC i -}