{-# LANGUAGE GADTs, StandaloneDeriving, NoImplicitPrelude, FlexibleInstances  #-}

module Cat where
import Control.Category
import Prelude hiding ((.), id)


class Category k => Monoidal k where
    parC :: k a c -> k b d -> k (a,b) (c,d)


class Monoidal k => Cartesian k where
    fstC :: k (a,b) a 
    sndC :: k (a,b) b 
    dupC :: k a (a,a) 

class Cartesian k => Closed k where
    applyC :: k (k a b,a) b 
    curryC :: k (a,b) c -> k a (k b c)
    uncurryC :: k a (k b c) -> k (a,b) c

fanC f g = (parC f g) . dupC

idC :: Category k => k a a
idC = id

data FreeCat a b where
    Comp :: FreeCat b c -> FreeCat a b -> FreeCat a c
    Id :: FreeCat a a
    Fst :: FreeCat (a,b) a
    Snd :: FreeCat (a,b) b
    Dup :: FreeCat a (a,a)
    Par :: FreeCat a b -> FreeCat c d -> FreeCat (a,c) (b,d)
    Add :: FreeCat (a,a) a
    Mul :: FreeCat (a,a) a

deriving instance Show (FreeCat a b)

instance Category FreeCat where
    (.) = Comp
    id = Id

instance Monoidal FreeCat where
    parC = Par

instance Cartesian FreeCat where
    fstC = Fst
    sndC = Snd
    dupC = Dup

instance Monoidal (->) where
    parC f g = \(x,y) -> (f x, g y)  

instance Cartesian (->) where
    fstC (x,y) = x
    sndC (x,y) = y
    dupC x = (x,x)

class Cartesian k => NumCat k where
    mulC :: Num a => k (a,a) a
    negateC :: Num a => k a a
    addC :: Num a => k (a,a) a
    subC :: Num a => k (a,a) a
    absC :: Num a => k a a

instance NumCat (->) where
    mulC = uncurry (*)
    negateC = negate
    addC = uncurry (+)
    subC = uncurry (-)
    absC = abs

instance NumCat FreeCat where
    mulC = Mul
    negateC = error "TODO"
    addC = Add
    subC = error "TODO"
    absC = error "TODO"

instance (NumCat k, Num a) => Num (k z a) where
    f + g = addC . (fanC f g)
    f * g = mulC . (fanC f g)
    negate f = negateC . f
    f - g = subC . (fanC f g)
    abs f = absC . f 
    signum = error "TODO"
    fromInteger = error "TODO"

