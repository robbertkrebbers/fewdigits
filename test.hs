{-# OPTIONS_GHC -fglasgow-exts #-}

import Data.Real.CReal
import Data.Real.DReal
import Data.Time

class PowerInt a where powerInt :: (Integral int) => a -> int -> a
instance PowerInt DReal where powerInt = drealPowerInt
instance PowerInt CReal where powerInt = realPowerInt

problems :: Floating a => PowerInt a => [(String, a)]
problems = [
  ("P01", sin (sin (sin 1))),
  ("P02", sqrt pi),
  ("P03", sin (exp 1)),
  ("P04", exp (pi * sqrt 163)),
  ("P05", exp (exp (exp 1))),
  ("P06", log (1 + log (1 + log (1 + log (1 + pi))))),
  ("P07", exp 1000),
  ("P08", cos (fromRational (10 ^ 50))),
  ("P09", sin (3 * log (640320) / sqrt 163)),
  ("P11", tan (exp 1) + atan (exp 1) + tanh (exp 1) + atanh (recip (exp 1))),
  ("P12", asin (recip (exp 1)) + cosh (exp 1) + asinh (exp 1)),
  ("C01", sin (tan (cos 1))),
  ("C02", sqrt (exp 1 / pi)),
  ("C03", sin (powerInt (exp 1 + 1) 3)),
  ("C04", exp (pi * sqrt 2011)),
  ("C05", exp (exp (sqrt (exp 1)))),
  ("C06", atanh (1 - atanh (1 - atanh (1 - atanh (recip pi))))),
  ("C07", powerInt pi 1000),
  ("C09", sin (10 * atanh (tanh (pi * (sqrt 2011) / 3)))),
  ("C11", tan (sqrt 2) + atanh (sin 1)),
  ("C12", asin (recip (exp 2)) + asinh (exp 2))]

main :: IO ()
main = do
  doProblems problems' 500
  
  where
   problems' :: [(String, DReal, CReal)]
   problems' = zipWith (\(nameD, expD) (nameC, expC) -> (nameD, expD, expC)) problems problems
   
   doProblems :: [(String, DReal, CReal)] -> Int -> IO ()
   doProblems [] _ = return ()
   doProblems ((name, expD, expC) : ps) n = do
    t0 <- getCurrentTime
    return $! danswer n expD
    t1 <- getCurrentTime
    return $! answer n expC
    t2 <- getCurrentTime
    putStrLn $ name ++ ", n=" ++ show n 
      ++ ", D=" ++ show (diffUTCTime t1 t0) 
      ++ ", C=" ++ show (diffUTCTime t2 t1)
    doProblems ps n

