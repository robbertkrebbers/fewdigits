{-# OPTIONS -XTypeOperators #-}
{-# OPTIONS -XTypeSynonymInstances #-}

module Data.Real.DReal 
where

import Data.Real.Dyadic
import Data.Real.Complete
import Data.Ratio
import Data.Bits
import Control.Exception
import Combinatorics
import Data.Interval
import Debug.Trace

toQ :: Dyadic -> Rational
toQ (Dyadic m e) = if e >= 0
  then fromInteger (shiftL m (toEnum e))
  else (fromInteger m) / (fromInteger (shiftR 1 (toEnum e)))

toStage :: Gauge -> Int
toStage 0 = error "toStage of 0"
toStage q = ilogb 2 (denominator q `div` numerator q) + 1

type DReal = Complete Dyadic

dinject :: Dyadic -> DReal
dinject = unit

dcompress :: DReal -> DReal
dcompress x eps = 
  let d = (x (eps/2))
  in if (expo d <= 0) then dnormalize (toStage (eps/2)) d else d

mapDR :: (Dyadic :=> Dyadic) -> DReal -> DReal
mapDR f x = dcompress $ mapC f x

mapDR2 :: (Dyadic :=> Dyadic :=> Dyadic) -> DReal -> DReal -> DReal
mapDR2 f x y = dcompress $ mapC2 f x y

bindDR :: (Dyadic :=> DReal) -> DReal -> DReal
bindDR f x = dcompress $ bind f x

-- Negate
drealNegate :: DReal -> DReal
drealNegate = mapDR $ mkUniformCts id negate

-- Plus
dplusBaseCts :: Dyadic -> Dyadic :=> Dyadic
dplusBaseCts a = mkUniformCts id (a+)

drealTranslate :: Dyadic -> DReal -> DReal
drealTranslate a = mapDR (dplusBaseCts a)

dplusCts :: Dyadic :=> Dyadic :=> Dyadic
dplusCts = mkUniformCts id dplusBaseCts

drealPlus :: DReal -> DReal -> DReal
drealPlus = mapDR2 dplusCts

-- Mult
dmultBaseCts :: Dyadic -> Dyadic :=> Dyadic
dmultBaseCts 0 = constCts 0
dmultBaseCts c = mkUniformCts mu (c*)
  where
   mu eps = eps / (toQ (abs c))
  
drealScale :: Dyadic -> DReal -> DReal
drealScale 0 = \_ -> 0
drealScale c = mapDR (dmultBaseCts c)

dBoundAbs :: Dyadic -> Dyadic -> Dyadic
dBoundAbs c = min c . max (-c)

dBoundAbsUniformCts :: Dyadic -> Dyadic :=> Dyadic
dBoundAbsUniformCts c = mkUniformCts id (dBoundAbs c)

dmultUniformCts :: Dyadic -> Dyadic :=> Dyadic :=> Dyadic
dmultUniformCts maxy = mkUniformCts mu (\x -> dmultBaseCts x `o` dBoundAbsUniformCts maxy)
  where
   mu eps = assert (maxy > 0) (eps / (toQ maxy))

drealMultBound :: Dyadic -> DReal -> DReal -> DReal
drealMultBound b = mapDR2 (dmultUniformCts b)

drealMult :: DReal -> DReal -> DReal
drealMult x y = mapDR2 (dmultUniformCts b) x y
  where
   b = abs (y 1) + 1

-- Misc
dapproxRange :: DReal -> Dyadic -> Interval Dyadic
dapproxRange x eps = Interval (r - eps, r + eps)
  where 
   r = x (toQ eps)

dproveNonZeroFrom :: Int -> DReal -> Dyadic
dproveNonZeroFrom k x | high < 0  = high
                      | 0 < low   = low
                      | otherwise = dproveNonZeroFrom (32 + k) x
 where
  eps = Dyadic 1 (-k)
  Interval (low, high) = dapproxRange x eps

dproveNonZero :: DReal -> Dyadic
dproveNonZero x = dproveNonZeroFrom 0 x 

dabsCts = mkUniformCts id abs

drealAbs :: DReal -> DReal
drealAbs = mapDR dabsCts

instance Eq DReal where
  a == b = 0 == dproveNonZero (drealPlus a (drealNegate b))
 
instance Num DReal where
  (+) = drealPlus
  (*) = drealMult
  negate = drealNegate
  abs = drealAbs
  signum = \x -> 0
  fromInteger = dinject . fromInteger
 
-- Inv
dInv :: Dyadic -> DReal
dInv x eps = dinv (toStage eps) x

dInvBaseCts :: Dyadic -> Dyadic :=> DReal
dInvBaseCts nonZero = mkUniformCts mu f
  where
   f x | 0 <= nonZero = dInv (max nonZero x)
       | otherwise    = dInv (min nonZero x)
   mu eps = toQ (nonZero * nonZero) * eps

drealInvWitness :: Dyadic -> DReal -> DReal
drealInvWitness nonZero = bindDR $ dInvBaseCts nonZero

drealInv :: DReal -> DReal
drealInv x = drealInvWitness (dproveNonZero x) x

instance Fractional DReal where
  recip = drealInv
  fromRational x = fromInteger (numerator x) * recip (fromInteger (denominator x))
 
-- Int pow
dintPowerCts :: (Integral int) => Dyadic -> int -> Dyadic :=> Dyadic
dintPowerCts _ 0 = constCts 1
dintPowerCts maxx n = mkUniformCts mu (\x -> (dBoundAbs x maxx)^n)
  where
   mu eps = assert (maxx > 0) $ eps / (fromIntegral n * (toQ maxx)^(n-1))

drealPowerIntBound :: (Integral int) => Dyadic -> DReal -> int -> DReal
drealPowerIntBound b x n = mapDR (dintPowerCts b n) x

drealPowerInt :: (Integral int) => DReal -> int -> DReal
drealPowerInt x = drealPowerIntBound b x
  where
   b = abs (x 1) + 1

{- 
 Computes x_0 / a_0 - x_1 / a_1 + x_2 / a_2 - x_3 / a_3 + ...
  
 The input should meet the following conditions:
 * lim i->inf (x_i / a_i) = 0 
 * x_i / a_i >= x_i+1 / a_i+1 >= 0 
-}
dAltSum :: [Dyadic] -> [Dyadic] -> DReal
dAltSum xs as eps =
  sum k xs as
  where
   s = toStage eps
   k = sumlength 1 (tail xs) (tail as) + 1
   
   {-
    Compute the length of the prefix of X = x_0 / a_0 - x_1 / a_1 + ... that has
    to be computed in order to obtain an approximate X with precision eps/2. We 
    have to compute this length separately because it is mutually dependent with
    the precision of the divisions.
    
    We do this by computing a k such that (x_k / a_k)^(eps/(2k)) < eps/2 - eps/(2k)
   -}
   sumlength :: Int -> [Dyadic] -> [Dyadic] -> Int
   sumlength l (x : xs) (a : as) = 
     let delta = ddiv ((s + 1) + ((ilogb 2 . toEnum) l + 1)) x a
     in if delta < Dyadic 1 (((ilogb 2 . toEnum) l + 1) - (s + 1))
       then l 
       else sumlength (l + 1) xs as 
   {-
   sumlength :: Int -> [Dyadic] -> [Integer] -> Int
   sumlength l (x : xs) (f : fs) = 
     let delta = toQ (ddiv (toStage (eps / (2 * toEnum l))) x (fromInteger f))
     in if delta < eps / 2 - eps / (2 * toEnum l)
       then l 
       else sumlength (l + 1) xs fs -}
       
   {- 
    Given [x1, ... xn] [a1, ... an], compute the alternating sum of xi / ai
    A total error of eps/2 is allowed, so we approximate each coordinate with a 
    precision of eps/(2k).
   -}
   sum :: Int -> [Dyadic] -> [Dyadic] -> Dyadic
   sum 0 _ _ = 0
   sum l (x : xs) (a : as) = ddiv ((s + 1) + k) x a - sum (l - 1) xs as

-- Exp
dpowers :: Dyadic -> [Dyadic]
dpowers d = iterate (*d) 1

radius = Dyadic 2 (-51)

dSmallExpNeg :: Dyadic -> DReal
dSmallExpNeg x = assert (-1 <= x && x <= 0) $ dAltSum (dpowers (-x)) (map fromInteger factorials)

dExpNeg :: Dyadic -> DReal
dExpNeg x | -radius <= x = dSmallExpNeg x
          | otherwise    = drealPowerInt (dExpNeg (dshift x (-1))) 2

dExp :: Dyadic -> DReal
dExp x | 0 <= x    = recip (dExpNeg (-x))
       | otherwise = dExpNeg x

dExpUniformCts :: Integer -> Dyadic :=> DReal
dExpUniformCts upperBound = mkUniformCts mu (dExp . min (fromInteger upperBound))
  where
   mu eps | upperBound <= 0 = eps * 2 ^ (-upperBound)
          | otherwise       = eps / (3 ^ upperBound)

drealExp :: DReal -> DReal
drealExp x = bindDR (dExpUniformCts b) x
  where 
   b :: Integer
   b = ceiling (toQ (x 1)) + 1

-- arctan
oddElements :: [a] -> [a]
oddElements (x : _ : l) = x : oddElements l
oddElements l = l

positives :: Num a => [a]
positives = series 1
  where 
   series :: Num a => a -> [a]
   series n = n : series (n + 1)

{- Computes arctan (n / d). Only valid for n / d < 1 / 2 -}
dSmallArcTan :: Dyadic -> Dyadic -> DReal
dSmallArcTan n d = assert (abs n < d * Dyadic 1 (-1)) $
  dAltSum (oddElements $ tail $ dpowers n) (oddElements $ zipWith (*) positives (tail $ dpowers d))

dArcTan :: Dyadic -> DReal
dArcTan x | x <= Dyadic (-1) (-1) = negate $ posArcTan $ negate x
          | otherwise             = posArcTan x
  where
   {- Requires (-1/2) < x-}
   posArcTan x | 2 < x              = drealPi2 - dSmallArcTan 1 x
               | Dyadic 1 (-1) <= x = drealPi4 + dSmallArcTan (x - 1) (x + 1)
               | otherwise          = dSmallArcTan x 1

drealArcTan :: DReal -> DReal
drealArcTan = bindDR $ mkUniformCts id dArcTan

-- Pi
dScalePi :: Dyadic -> DReal
dScalePi x = 
 ((drealScale (x * 176) (dSmallArcTan 1 57)) + 
  (drealScale (x * 28) (dSmallArcTan 1 239))) +
 ((drealScale (x * negate 48) (dSmallArcTan 1 682)) +
  (drealScale (x * 96) (dSmallArcTan 1 12943)))

dreal2Pi = dScalePi 2
drealPi = dScalePi 1
drealPi2 = dScalePi (Dyadic 1 (-1))
drealPi4 = dScalePi (Dyadic 1 (-2))

{- Computes sin (n / d) -}
dSmallSin :: Dyadic -> Dyadic -> DReal
dSmallSin n d = dAltSum 
  (oddElements $ tail $ dpowers n) 
  (oddElements $ tail $ zipWith (*) (map fromInteger factorials) (dpowers d))

dSin :: Dyadic -> Dyadic -> DReal
dSin n d | n * d < 0               = negate $ dSin (negate n) d
         | radius * abs d <= abs n = f $ dSin n (3 * d)
         | otherwise               = dSmallSin n d
  where
   f :: DReal -> DReal
   f = mapDR $ mkUniformCts (\eps -> eps / 9) (\x -> x * (3 - dshift (x*x) 2))

drealSinWithInv :: DReal -> Dyadic -> DReal
drealSinWithInv x d = (bindDR $ mkUniformCts id $ \n -> dSin n d) x

drealSin :: DReal -> DReal
drealSin x = drealSinWithInv x 1

{-
 The following definition, which is inspired by the definition in CoRN, 
 should be faster. But in practice, calculating Pi and computing the 
 approximation, turns out to be too expensive.
-}
drealFastSin :: DReal -> DReal
drealFastSin x = drealSin $ x - drealScale (2 * n) drealPi
  where
   n = fromInteger $ ceiling $ toQ $ x 1 * recip dreal2Pi (1/1000)

-- cos
drealCos :: DReal -> DReal
drealCos x = f $ drealSinWithInv x 2
  where
   f :: DReal -> DReal
   f = mapDR $ mkUniformCts (\eps -> eps / 4) (\x -> 1 - dshift (x * x) 1)

-- sqrt
dSmallWolframSqrt :: Dyadic -> DReal
dSmallWolframSqrt n eps = dshift (vf*ef) (-3)
  where
   (_,vf,ef) = until (\(u,v,e) -> toQ e <= eps) wolfram (n, 0, 4)
   wolfram (u,v,e) | u >= v + 1 = (dshift (u-v-1) 2, dshift (v+2) 1, dshift e (-1))
                   | otherwise = (dshift u 2, dshift v 1, dshift e (-1))

{-
drealSmallNewtonSqrt :: Dyadic -> DReal
drealSmallNewtonSqrt x = drealScale x (join bounded)
  where
   f :: Dyadic -> Dyadic
   f r = r + r * dshift (1 - r^2 * x) (-1)
   
   fCts :: Dyadic :=> Dyadic
   fCts = mkUniformCts (\e -> 2 / 9 * e) f

   bounded :: Complete DReal
   bounded eps = (iterate (mapDR fCts) 1 !! k)
    where
     (k,_) = until (\(_,e) -> e <= eps) (\(i,e) -> (i+1, e^2)) (2, 1/2)
-}

drealSmallNewtonSqrt :: Dyadic -> DReal
drealSmallNewtonSqrt x = join bounded
  where
   f :: Dyadic -> DReal
   f r eps = dshift (r + ddiv (toStage eps) x r) (-1)
   
   fCts :: Dyadic :=> DReal
   fCts = mkUniformCts (\e -> 1 / 3 * e) f

   bounded :: Complete DReal
   bounded eps = (iterate (bind fCts) 1 !! k)
    where
     (k,_) = until (\(_,e) -> e <= eps) (\(i,e) -> (i+1, e^2 / 2)) (2, 1/2)

dBigSqrt :: (Dyadic -> DReal) -> Dyadic -> DReal
dBigSqrt f n | n < 1     = drealScale (Dyadic 1 (-1)) (dBigSqrt f (dshift n 2))
             | 4 <= n    = drealScale 2 (dBigSqrt f (dshift n (-2)))
             | otherwise = f n

dSqrtCts :: (Dyadic -> DReal) -> Dyadic :=> DReal
dSqrtCts f = mkUniformCts (^2) (dBigSqrt f)

drealBigSqrt :: (Dyadic -> DReal) -> DReal -> DReal
drealBigSqrt f = bindDR (dSqrtCts f)
  
drealWolframSqrt :: DReal -> DReal
drealWolframSqrt = drealBigSqrt dSmallWolframSqrt

drealNewtonSqrt :: DReal -> DReal
drealNewtonSqrt = drealBigSqrt drealSmallNewtonSqrt

{- Computes ln(n / d). Only valid for 1 <= n / d < 2 -}
dSmallLn :: Dyadic -> Dyadic -> DReal
dSmallLn n d = assert (1 * d <= n && n < 2 * d) $ dAltSum 
  (tail $ dpowers (n - d)) 
  (zipWith (*) (tail $ dpowers d) positives)

{- Requires that 0 < x -}
dLn :: Dyadic -> DReal
dLn x | x < 1     = negate (posLn 1 x)
      | otherwise = posLn x 1
 where
  ln43 = dSmallLn 4 3
  ln2 = wideLn 2 1
  {- good for 1 <= n/d <= 2 -}
  wideLn n d | 2 * n < 3 * d = dSmallLn n d
             | otherwise     = dSmallLn (3 * n) (4 * d) + ln43
  {- requires that 1 <= n/d -}
  posLn n d = wideLn n d' + drealScale m ln2
   where
    (d',m) = until (\(d,m) -> n <= d * 2) (\(d,m) -> (d * 2,m + 1)) (d,0)

{- domain is [nonZero, inf) -}
dLnUniformCts :: Dyadic -> Dyadic :=> DReal
dLnUniformCts nonZero = assert (0 < nonZero) $ mkUniformCts mu (\x -> dLn (max x nonZero))
  where
   mu eps = eps * toQ nonZero

drealLnWitness :: Dyadic -> DReal -> DReal
drealLnWitness nonZero = bindDR $ dLnUniformCts nonZero

drealLn :: DReal -> DReal
drealLn x = drealLnWitness (dproveNonZero x) x

instance Floating DReal where
  exp = drealExp
  log = drealLn
  pi = drealPi
  sin = drealSin
  cos = drealCos
  atan = drealArcTan
  sqrt = drealNewtonSqrt
  sinh x = drealScale (Dyadic 1 (-1)) (exp x - exp (-x))
  cosh x = drealScale (Dyadic 1 (-1)) (exp x + exp (-x))
  asin x = atan (x/sqrt(drealTranslate 1 (negate (drealPowerInt x 2))))
  acos x = drealPi2 - asin x
  acosh x = log (x+sqrt(drealTranslate (-1) (drealPowerInt x 2)))
  asinh x = log (x+sqrt(drealTranslate 1 (drealPowerInt x 2)))
  atanh x = drealScale (Dyadic 1 (-1))
    (log ((drealTranslate 1 x) / (drealTranslate 1 (negate x))))

danswer :: Int -> DReal -> String
danswer n x = show (round $ toQ $ drealScale (10^n) x (1 / 2)) ++ "x10^-" ++ (show n)

instance Show DReal where
  show = danswer 50
