{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module Data.Barbie.Internal.Constraints
  ( DictOf(..)
  , DictOfBare(..)
  , ClassInstanceDictF(..)

  , ConstraintsB(..)

  , CanDeriveGenericInstance
  , ConstraintsOfMatchesGenericDeriv
  , GConstraintsOf
  , GAdjProof
  , gadjProofDefault
  )

where

import Data.Barbie.Internal.Classification (BarbieType(..), ClassifyBarbie, GClassifyBarbie)
import Data.Barbie.Internal.Functor(FunctorB(..))
import Data.Barbie.Internal.Generics
import Data.Barbie.Internal.Tags(F, PxF)
import Data.Barbie.Internal.Wear(Bare)

import Data.Functor.Classes(Show1(..))
import Data.Functor.Product(Product(..))
import Data.Kind(Constraint)

import Data.Proxy

import GHC.Generics


-- | @'DictOf' c f a@ is evidence that there exists an instance
--   of @c (f a)@.
data DictOf c f a where
  PackedDict :: c (f a) => DictOf c f a


instance Eq (DictOf c f a) where
  _ == _ = True

instance Show (DictOf c f a) where
  showsPrec _ PackedDict = showString "PackedDict"

instance Show1 (DictOf c f) where
  liftShowsPrec _ _ = showsPrec


-- | @'DictOfBare' c a@  is evidence that there exists an
--   instance of @c a@.
data DictOfBare c a where
  PackedDictBare :: c a => DictOfBare c a


instance Eq (DictOfBare c a) where
  _ == _ = True

instance Show (DictOfBare c a) where
  showsPrec _ PackedDictBare = showString "PackedDictBare"

instance Show1 (DictOfBare c) where
  liftShowsPrec _ _ = showsPrec


data NoDict a
  = NoDict
  deriving(Eq, Show)

instance Show1 NoDict where
  liftShowsPrec _ _ = showsPrec


class ClassInstanceDictF d where
  type ConstraintOfDict d a :: Constraint

  -- | Pack the dictionary associated with an instance.
  packDict :: ConstraintOfDict d a => d a


  -- | Turn a constrained-function into an unconstrained one
  --   that uses the packed instance dictionary instead.
  requiringDict :: (ConstraintOfDict d a => r) -> (d a -> r)


instance ClassInstanceDictF (DictOf c f) where
  type ConstraintOfDict (DictOf c f) a = c (f a)
  packDict = PackedDict
  requiringDict r = \PackedDict -> r

instance ClassInstanceDictF (DictOfBare c)  where
  type ConstraintOfDict (DictOfBare c) a = c a
  packDict = PackedDictBare
  requiringDict r = \PackedDictBare -> r

instance ClassInstanceDictF NoDict  where
  type ConstraintOfDict NoDict a = ()
  packDict = NoDict
  requiringDict r = \NoDict -> r


-- | Example definition:
  --
  -- @
  -- data T f = A (f 'Int') (f 'String') | B (f 'Bool') (f 'Int')
  --
  -- instance 'ConstraintsB' T where
  --   type 'ConstraintsOf' c f T = (c (f 'Int'), c (f 'String'), c (f 'Bool'))
  -- @
  --
  -- There is a default implementation of 'ConstraintsOf' for
  -- 'Generic' types, so in practice one can simply do:
  --
  -- @
  -- derive instance 'Generic' T
  -- instance 'ConstraintsB' T
  -- @
class FunctorB b => ConstraintsB b where
  -- | @'ConstraintsOf' c f b@ should contain a constraint @c (f x)@
  --  for each @f x@ occurring in @b@. E.g.:
  --
  -- @
  -- 'ConstraintsOf' 'Show' f Barbie = ('Show' (f 'String'), 'Show' (f 'Int'))
  -- @
  type ConstraintsOf (c :: * -> Constraint) (f :: * -> *) b :: Constraint
  type ConstraintsOf c f b = GConstraintsOf c f (RecRep (b (Target F)))

  type ProofOfInstanceFor (c :: * -> Constraint) (f :: * -> *) b :: * -> *
  type ProofOfInstanceFor c f b = GProofOfInstance c f (RecRep (b (Target F)))

  -- | Adjoint a proof-of-instance to a barbie-type.
  adjProof
    ::  forall c f
    .  (ConstraintsOf c f b , ClassInstanceDictF (ProofOfInstanceFor c f b))
    => Proxy c -> b f -> b (Product (ProofOfInstanceFor c f b) f)

  default adjProof
    :: forall c f
    .  ( CanDeriveGenericInstance b
       , ConstraintsOfMatchesGenericDeriv c f b
       , ConstraintsOf c f b
       )
    => Proxy c -> b f -> b (Product (ProofOfInstanceFor c f b) f)
  adjProof = gadjProofDefault

-- | Intuivively, the requirements to have @'ConstraintsB' B@ derived are:
--
--     * There is an instance of @'Generic' (B f)@ for every @f@
--
--     * If @f@ is used as argument to some type in the definition of @B@, it
--       is only on a Barbie-type with a 'ConstraintsB' instance.
type CanDeriveGenericInstance b
  = ( Generic (b (Target F))
    , Generic (b (Target PxF))
    , GAdjProof (ClassifyBarbie b) b (RecRep (b (Target F)))
    , Rep (b (Target PxF)) ~ Repl' (Target F) (Target PxF) (RecRep (b (Target F)))
    )

type ConstraintsOfMatchesGenericDeriv c f b
  = ( ConstraintsOf c f b ~ GConstraintsOf c f (RecRep (b (Target F)))
    , ConstraintsOf c f b ~ ConstraintByType (ClassifyBarbie b) c f (RecRep (b (Target F)))
    , ClassInstanceDictF (ProofOfInstanceByType (ClassifyBarbie b) c f)
    )


-- ===============================================================
--  Generic derivations
-- ===============================================================

type family ConstraintByType bt (c :: * -> Constraint) (f :: * -> *) r :: Constraint where
  ConstraintByType bt c f (M1 _i _c x) = ConstraintByType bt c f x
  ConstraintByType bt c f V1 = ()
  ConstraintByType bt c f U1 = ()
  ConstraintByType bt c f (l :*: r) = (ConstraintByType bt c f l, ConstraintByType bt c f r)
  ConstraintByType bt c f (l :+: r) = (ConstraintByType bt c f l, ConstraintByType bt c f r)
  ConstraintByType 'WearBarbie c f (K1 R (NonRec (Target (W F) a))) = ConstraintOfDict (ProofOfInstanceByType 'WearBarbie c f) a
  ConstraintByType 'NonWearBarbie c f (K1 R (NonRec (Target (W F) a))) = ConstraintOfDict (ProofOfInstanceByType 'NonWearBarbie c f) a
  ConstraintByType 'WearBarbie c f (K1 R (NonRec (Target F a))) = ConstraintOfDict (ProofOfInstanceByType 'WearBarbie c f) a
  ConstraintByType 'NonWearBarbie c f (K1 R (NonRec (Target F a))) = ConstraintOfDict (ProofOfInstanceByType 'NonWearBarbie c f) a
  ConstraintByType bt c f (K1 R (NonRec (b (Target F)))) = ConstraintsOf c f b
  ConstraintByType bt c f (K1 R (RecUsage (b (Target F)))) = () -- break recursion
  ConstraintByType bt c f (K1 _i _c) = ()

type GConstraintsOf c f r
  = ConstraintByType (GClassifyBarbie r) c f r


type family ProofOfInstanceByType bt c f where
  ProofOfInstanceByType 'NoBarbie c f      = NoDict
  ProofOfInstanceByType 'WearBarbie c Bare = DictOfBare c
  ProofOfInstanceByType 'WearBarbie c f    = DictOf c f
  ProofOfInstanceByType 'NonWearBarbie c f = DictOf c f

type GProofOfInstance c f r
  = ProofOfInstanceByType (GClassifyBarbie r) c f


-- | Default implementation of 'adjProof' based on 'Generic'.
gadjProofDefault
  :: forall b c f
  . ( CanDeriveGenericInstance b
    , ConstraintsOfMatchesGenericDeriv c f b
    , ConstraintsOf c f b
    )
  => Proxy c -> b f -> b (Product (ProofOfInstanceFor c f b) f)
gadjProofDefault _ b
  = unsafeUntargetBarbie @PxF $ to $
      gadjProof pcbf pbt $ fromWithRecAnn (unsafeTargetBarbie @F b)
  where
    pcbf = Proxy :: Proxy (c (b f))
    pbt  = Proxy :: Proxy (ClassifyBarbie b)


class GAdjProof (bt :: BarbieType) b rep where
  gadjProof
    :: ( ConstraintByType bt c f rep
       , GConstraintsOf c f (RecRep (b (Target F))) -- for the recursive case!
       , ClassInstanceDictF (ProofOfInstanceByType bt c f)
       )
    => Proxy (c (b f))
    -> Proxy bt
    -> rep x
    -> Repl' (Target F) (Target PxF) rep x


-- ----------------------------------
-- Trivial cases
-- ----------------------------------

instance GAdjProof bt b x => GAdjProof bt b (M1 _i _c x) where
  {-# INLINE gadjProof #-}
  gadjProof pcbf pbt (M1 x)
    = M1 (gadjProof pcbf pbt x)

instance GAdjProof bt b V1 where
  gadjProof _ _ _ = undefined

instance GAdjProof bt b U1 where
  {-# INLINE gadjProof #-}
  gadjProof _ _ u1 = u1

instance (GAdjProof bt b l, GAdjProof bt b r) => GAdjProof bt b (l :*: r) where
  {-# INLINE gadjProof #-}
  gadjProof pcbf pbt (l :*: r)
    = (gadjProof pcbf pbt l) :*: (gadjProof pcbf pbt r)

instance (GAdjProof bt b l, GAdjProof bt b r) => GAdjProof bt b (l :+: r) where
  {-# INLINE gadjProof #-}
  gadjProof pcbf pbt = \case
    L1 l -> L1 (gadjProof pcbf pbt l)
    R1 r -> R1 (gadjProof pcbf pbt r)


-- -- --------------------------------
-- -- The interesting cases
-- -- --------------------------------

instance {-# OVERLAPPING #-} GAdjProof 'WearBarbie b (K1 R (NonRec (Target (W F) a))) where
  {-# INLINE gadjProof #-}
  gadjProof pcbf _ (K1 (NonRec fa))
    = K1 $ unsafeTarget @(W PxF) (Pair (mkProof pcbf) $ unsafeUntarget @(W F) fa)
    where
      mkProof
        :: ( ClassInstanceDictF (ProofOfInstanceByType 'WearBarbie c f)
           , ConstraintOfDict (ProofOfInstanceByType 'WearBarbie c f) a
           )
        => Proxy (c (b f))
        -> ProofOfInstanceByType 'WearBarbie c f a
      mkProof _ = packDict


instance {-# OVERLAPPING #-} GAdjProof 'WearBarbie b (K1 R (NonRec (Target F a))) where
  {-# INLINE gadjProof #-}
  gadjProof pcbf _ (K1 (NonRec fa))
    = K1 $ unsafeTarget @PxF (Pair (mkProof pcbf) $ unsafeUntarget @F fa)
    where
      mkProof
        :: ( ClassInstanceDictF (ProofOfInstanceByType 'WearBarbie c f)
           , ConstraintOfDict (ProofOfInstanceByType 'WearBarbie c f) a
           )
        => Proxy (c (b f))
        -> ProofOfInstanceByType 'WearBarbie c f a
      mkProof _ = packDict

instance {-# OVERLAPPING #-} GAdjProof 'NonWearBarbie b (K1 R (NonRec (Target F a))) where
  {-# INLINE gadjProof #-}
  gadjProof pcbf _ (K1 (NonRec fa))
    = K1 $ unsafeTarget @PxF (Pair (mkProof pcbf) $ unsafeUntarget @F fa)
    where
      mkProof
        :: ( ClassInstanceDictF (ProofOfInstanceByType 'NonWearBarbie c f)
           , ConstraintOfDict (ProofOfInstanceByType 'NonWearBarbie c f) a
           )
        => Proxy (c (b f))
        -> ProofOfInstanceByType 'NonWearBarbie c f a
      mkProof _ = packDict


-- instance {-# OVERLAPPING #-} CanDeriveGenericInstance b => GAdjProof b (K1 R (RecUsage (b (Target F)))) where
--   {-# INLINE gadjProof #-}
--   gadjProof pcbf (K1 (RecUsage bf))
--     = K1 $ to $ gadjProof pcbf $ fromWithRecAnn bf

-- instance {-# OVERLAPPING #-} ConstraintsB b' => GAdjProof b (K1 R (NonRec (b' (Target F)))) where
--   {-# INLINE gadjProof #-}
--   gadjProof pcbf (K1 (NonRec bf))
--     = K1 $ unsafeTargetBarbie @PxF $ adjProof' pcbf $ unsafeUntargetBarbie @F bf
--     where
--       adjProof'
--         :: ConstraintsOf c f b'
--         => Proxy (c (b f)) -> b' f -> b' (Product (DictOf c f) f)
--       adjProof' _ = adjProof

instance (K1 i a) ~ Repl' (Target F) (Target PxF) (K1 i (NonRec a)) => GAdjProof bt b (K1 i (NonRec a)) where
  {-# INLINE gadjProof #-}
  gadjProof _ _ (K1 (NonRec a)) = K1 a
