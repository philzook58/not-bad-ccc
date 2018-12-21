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
    ScopedTypeVariables #-}
module CCC (
     toCCC,
     pleasefire )where

import Control.Category
import Prelude hiding ((.), id)
import Cat
-- import Prelude (Bool(..))


{-# INLINE [2] _parC #-}
_parC :: Monoidal k => k a c -> k b d -> k (a,b) (c,d)
_parC = parC

{-# INLINE [2] _fstC #-}
_fstC :: Cartesian k => k (a,b) a
_fstC = fstC

{-# INLINE [2] _sndC #-}
_sndC :: Cartesian k => k (a,b) b
_sndC = sndC

{-# INLINE [2] _dupC #-}
_dupC :: Cartesian k => k a (a,a)
_dupC = dupC

{-# INLINE [2] _idC #-}
_idC :: Category (k :: * -> * -> *) => k a a
_idC = idC

{-# INLINE [2] _fanC #-}
_fanC f g = (_parC f g) .% _dupC

{-# INLINE [2] _comp #-}
_comp :: Category k => k b c -> k a b -> k a c
_comp = (.)

{-# INLINE [2] (.%) #-}
(.%) :: Category k => k b c -> k a b -> k a c
(.%) = (.)

{-# RULES
"identity/left"  forall p. _idC . p = p
"identity/right"  forall p. p . _idC = p
"fst . diag"    _fstC . _dupC = _idC
"snd . diag"    _sndC . _dupC = _idC
"fst . f *** g" forall f g. _fstC . (_parC f g) = f . _fstC
"snd . f *** g" forall f g. _sndC . (_parC f g) = g . _sndC
"fst . f &&& g" forall f g. _fstC . (_fanC f g) = f 
"snd . f &&& g" forall f g. _sndC . (_fanC f g) = g
"snd . f &&& g" forall f g. _sndC . (_fanC f g) = g
"parC fst snd"    (_parC _fstC _sndC) . _dupC = _idC
"parC dupC"     forall f. (_parC f f) . _dupC = _dupC . f
"association"   forall p q r . (p . q) . r = p . (q . r)
"_association"   forall p q r . (p `_comp` q) `_comp` r = p `_comp` (q `_comp` r)
  #-}

{-# RULES
"identity/left"  forall p. _idC .% p = p
"identity/right"  forall p. p .% _idC = p
"fst . diag"    _fstC .% _dupC = _idC
"snd . diag"    _sndC .% _dupC = _idC
"fst . f *** g" forall f g. _fstC .% (_parC f g) = f .% _fstC
"snd . f *** g" forall f g. _sndC .% (_parC f g) = g .% _sndC
"fst . f &&& g" forall f g. _fstC .% (_fanC f g) = f 
"snd . f &&& g" forall f g. _sndC .% (_fanC f g) = g
"snd . f &&& g" forall f g. _sndC .% (_fanC f g) = g
"parC fst snd"    (_parC _fstC _sndC) .% _dupC = _idC
"parC dupC"     forall f. (_parC f f) .% _dupC = _dupC .% f
"association"   forall p q r . (p .% q) .% r = p .% (q .% r)

  #-}
{-# INLINE [1] pleasefire #-}
pleasefire :: Cartesian k => k (a,b) (a,b)
pleasefire =  (_parC _fstC _sndC) .% _dupC 

pleasefire2 :: Cartesian k => k (a,b) (a,b) 
pleasefire2 = _sndC .% _dupC

pleasefire3 :: Cartesian k => k (a,b) (a,b) 
pleasefire3 = pleasefire .% _idC

 {- Could we grab || with a rewrite rule? -}




class IsTup a b | a -> b
instance {-# INCOHERENT #-} (c ~ 'True) => IsTup (a,b) c
instance {-# INCOHERENT #-} (b ~ 'False) => IsTup a b


class BuildInput tup (flag :: Bool) path where
    buildInput :: path -> tup

instance (Cartesian k,
          IsTup a fa,
          IsTup b fb,
          BuildInput a fa (k x a'), 
          BuildInput b fb (k x b'),
          ((k x (a',b')) ~ cat)) =>  BuildInput (a,b) 'True cat where
    buildInput path = (buildInput @a @fa patha, buildInput @b @fb pathb) where
                 patha = _fstC .% path
                 pathb = _sndC .% path

instance (Category k, a ~ k a' b') => BuildInput a  'False (k a' b') where
    buildInput path = path


class FanOutput out (flag :: Bool) cat | out flag -> cat where
    fanOutput :: out -> cat

instance (Cartesian k,
         IsTup a fa,
         IsTup b fb,
         FanOutput a fa (k x a'),
         FanOutput b fb (k x b'),
         k x (a', b') ~ cat
         )
          => FanOutput (a, b) 'True cat where
    fanOutput (x,y) = _fanC (fanOutput @a @fa x) (fanOutput @b @fb y)

instance (Category k, kab ~ k a b) => FanOutput kab 'False (k a b) where
    fanOutput f = f 

toCCC :: forall k a b a' b' fa fb x. (IsTup a fa, IsTup b fb, Cartesian k, BuildInput a fa (k a' a'), FanOutput b fb (k a' b')) => (a -> b) -> k a' b'
toCCC f = fanOutput @b @fb output where
                                      input = buildInput @a @fa (_idC @k @a')
                                      output = f input

-- example7 = toCCC (\(x,(y,z)) -> (x,(y,z)))
{-
instance (NumCat k, Num a) => Num (k z a) where
    f + g = _addC . (_fanC f g)
    f * g = _mulC . (_fanC f g)
    negate f = _negateC . f
    f - g = _subC . (_fanC f g)
    abs f = _absC . f 
    signum = error "TODO"
    fromInteger = error "TODO"  

-}
                                    