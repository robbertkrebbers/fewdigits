{-# OPTIONS_GHC -fglasgow-exts #-}

import Data.Real.CReal
import Data.Real.DReal
import Data.Time

class PowerInt a where powerInt :: (Integral int) => a -> int -> a
instance PowerInt DReal where powerInt = drealPowerInt
instance PowerInt CReal where powerInt = realPowerInt

problems :: Floating a => PowerInt a => [(String, a, Int)]
problems = [
  ("P01", sin (sin (sin 1)), 100),
  ("P02", sqrt pi, 200),
  ("P03", sin (exp 1), 100),
  ("P04", exp (pi * sqrt 163), 100),
  ("P05", exp (exp (exp 1)), 100),
  ("P06", log (1 + log (1 + log (1 + log (1 + pi)))), 10),
  ("P07", exp 1000, 200),
  ("P08", cos (fromInteger (10 ^ 50)), 200),
  ("P09", sin (3 * log (640320) / sqrt 163), 100),
  ("P11", tan (exp 1) + atan (exp 1) + tanh (exp 1) + atanh (recip (exp 1)), 10),
  ("P12", asin (recip (exp 1)) + cosh (exp 1) + asinh (exp 1), 10),
  ("C01", sin (tan (cos 1)), 100),
  ("C02", sqrt (exp 1 / pi), 200),
  ("C03", sin (powerInt (exp 1 + 1) 3), 100),
  ("C04", exp (pi * sqrt 2011), 100),
  ("C05", exp (exp (sqrt (exp 1))), 100),
  ("C06", atanh (1 - atanh (1 - atanh (1 - atanh (recip pi)))), 10),
  ("C07", powerInt pi 1000, 400), 
  ("C09", sin (10 * atanh (tanh (pi * (sqrt 2011) / 3))), 7),
  ("C10", (7 + 2**(1/5) - 5 * 8**(1/5))**(1/3) + 4**(1/5) - 2**(1/5), 5),
  ("C11", tan (sqrt 2) + atanh (sin 1), 10),
  ("C12", asin (recip (exp 2)) + asinh (exp 2), 10)]

main :: IO ()
main = do
  doProblems problems' 50
  
  where
   problems' :: [(String, DReal, CReal, Int)]
   problems' = zipWith (\(nameD, expD,m) (_,expC,_) -> (nameD,expD,expC,m)) problems problems
   
   doProblems :: [(String, DReal, CReal, Int)] -> Int -> IO ()
   doProblems [] _ = return ()
   doProblems ((name, expD, expC, m) : ps) n = do
    t0 <- getCurrentTime
    return $! danswer (n * m) expD
    t1 <- getCurrentTime
    return $! answer (n * m) expC
    t2 <- getCurrentTime
    putStrLn $ name ++ ", n=" ++ show (n * m) 
      ++ ", D=" ++ show (diffUTCTime t1 t0) 
      ++ ", C=" ++ show (diffUTCTime t2 t1)
    doProblems ps n

