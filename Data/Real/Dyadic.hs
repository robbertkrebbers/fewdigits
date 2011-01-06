{- This code is derived from Andrej Bauer's implementation of the Reals using Dyadics -}

{- | This module contains a purely Haskell implementation of dyadic rationals, suitable
   for interval arithmetic. A faster implementation of dyadic rationals would use
   a fast arbitrary-precision floating-point library, such as MPFR and the related
   hmpfr Haskell bindings for it.
   
   A dyadic number is a rational whose denominator is a power of 2. 
-}

module Data.Real.Dyadic (
  Dyadic(..), ilogb, dnormalize, dToFloat, dinv, dlog2, dshift, ddiv
) where

import Data.Bits

-- | A dyadic number is of the form @m * 2^e@ where @m@ is the /mantissa/ and @e@ is the /exponent/.
data Dyadic = Dyadic { mant :: Integer, expo :: Int }

instance Show Dyadic where
  show (Dyadic m e) = show m ++ "*2^" ++ show e

shifted2 :: (Integer -> Integer -> a) -> Dyadic -> Dyadic -> a
shifted2 f (Dyadic m1 e1) (Dyadic m2 e2) =
  case compare e1 e2 of
    LT -> f m1 (shiftL m2 (e2-e1))
    EQ -> f m1 m2
    GT -> f (shiftL m1 (e1-e2)) m2

instance Eq Dyadic where
  a == b = shifted2 (==) a b
  a /= b = shifted2 (/=) a b

instance Ord Dyadic where
  compare a b = shifted2 compare a b

instance Num Dyadic where
  Dyadic m1 e1 + Dyadic m2 e2 = Dyadic m3 e3
      where m3 = if e1 < e2 then m1 + shiftL m2 (e2 - e1) else shiftL m1 (e1 - e2) + m2
            e3 = min e1 e2

  Dyadic m1 e1 - Dyadic m2 e2 = Dyadic m3 e3
      where m3 = if e1 < e2 then m1 - shiftL m2 (e2 - e1) else shiftL m1 (e1 - e2) - m2
            e3 = min e1 e2

  Dyadic m1 e1 * Dyadic m2 e2 = Dyadic (m1 * m2) (e1 + e2)

  abs (Dyadic m e) = Dyadic (abs m) e
  
  signum (Dyadic m e) = fromInteger (signum m)

  fromInteger i = Dyadic i 0


-- | This was taken from
-- | <http://www.haskell.org/pipermail/haskell-cafe/2008-February/039640.html>
-- | and it computes the integral logarithm in given base.
ilogb :: Integer -> Integer -> Int
ilogb b n | n < 0      = ilogb b (- n)
          | n < b      = 0
          | otherwise  = (up b n 1) - 1
  where up b n a = if n < (b ^ a)
                      then bin b (quot a 2) a
                      else up b n (2*a)
        bin b lo hi = if (hi - lo) <= 1
                         then hi
                         else let av = quot (lo + hi) 2
                              in if n < (b ^ av)
                                    then bin b lo av
                                    else bin b av hi

dlog2 (Dyadic m e) = e + ilogb 2 m
   
dnormalize :: Int -> Dyadic -> Dyadic
dnormalize s a@(Dyadic m e) = if e < -s 
  then Dyadic (shiftR m (-e - s)) (-s)
  else a
 
dToFloat (Dyadic m e) = encodeFloat m e

dinv :: Int -> Dyadic -> Dyadic
dinv _ (Dyadic 0 _) = 0
dinv s (Dyadic m e) = Dyadic (shiftL 1 (s + 1 - e) `div` m) (-(s + 1))

ddiv :: Int -> Dyadic -> Dyadic -> Dyadic
ddiv _ _ (Dyadic 0 _) = 0
ddiv s (Dyadic m1 e1) (Dyadic m2 e2) = Dyadic (shiftL m1 (s + 1 + e1 - e2) `div` m2) (-(s + 1))

dshift :: Dyadic -> Int -> Dyadic
dshift (Dyadic m e) k = Dyadic m (e + k)

