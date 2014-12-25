module CF where

-- http://rosettacode.org/wiki/Continued_fraction/Arithmetic/G(matrix_NG,_Contined_Fraction_N)#NG

-- represents the homographic transform
--          a1*z + a
-- f(z) --> --------
--          b1*z + b

import Data.Natural
import Data.List (inits)

data NG = NG {a1 :: Natural, a :: Natural, b1 :: Natural, b :: Natural}  deriving Show

output :: NG -> Bool
output (NG _ _ 0 _) = error "b1 == 0"
output (NG _ _ _ 0) = error "b == 0"
output (NG a1 a b1 b) = div a b == div a1 b1

term :: NG -> Natural
term (NG _ _ _ 0) = error "b == 0"
term (NG a1 a b1 b) = div a b

ingress :: NG -> Natural -> NG
ingress (NG a1 a b1 b) t = (NG (a + t * a1) a1 (b + t * b1) b1)

inf_ingress :: NG -> NG
inf_ingress (NG a1 _ b1 _) = NG a1 a1 b1 b1

egress :: NG -> Natural -> NG
egress (NG a1 a b1 b) t
 | t * b > a = error "t * b > a"
 | t * b1 > a1 = error "t * b1 > a1"
 | otherwise = NG b1 b (a1 - t * b1) (a - t * b)

type CF = [Natural]

ng_apply :: NG -> CF -> CF

ng_apply (NG _ _ 0 0) _ = []

ng_apply op@(NG a1 a b1 0) [] = ng_apply (inf_ingress op) []
ng_apply op@(NG a1 a 0 b) [] = ng_apply (inf_ingress op) []
ng_apply op@(NG a1 a b1 b) []
 | output op = let t = term op in t : (ng_apply (inf_ingress (egress op t)) [])
 | otherwise = ng_apply (inf_ingress op) []

ng_apply op@(NG a1 a b1 0) (x : xs) = ng_apply (ingress op x) xs
ng_apply op@(NG a1 a 0 b) (x : xs) = ng_apply (ingress op x) xs
ng_apply op@(NG a1 a b1 b) (x : xs)
 | output op = let t = term op in t : (ng_apply (ingress (egress op t) x) xs)
 | otherwise = ng_apply (ingress op x) xs

sqrt2 = 1 : (repeat 2)

e_constant = 2 : 1 : (e_pattern 2)
 where e_pattern n = n : 1 : 1 : (e_pattern (2 + n))

pi_constant :: [Natural]
pi_constant = [3, 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1, 14, 2, 1, 1, 2, 2, 2, 2, 1, 84, 2, 1, 1, 15, 3, 13, 1, 4, 2, 6, 6, 99, 1, 2, 2, 6, 3, 5, 1, 1, 6, 8, 1, 7, 1, 2, 3, 7, 1, 2, 1, 1, 12, 1, 1, 1, 3, 1, 1, 8, 1, 1, 2, 1, 6, 1, 1, 5, 2, 2, 3, 1, 2, 4, 4, 16, 1, 161, 45, 1, 22, 1, 2, 2, 1, 4, 1, 2, 24, 1, 2, 1, 3, 1, 2, 1]

r2cf :: Natural -> Natural -> CF
r2cf _ 0 = []
r2cf n d = q : (r2cf d r)
 where (q,r) = divMod n d

det :: NG -> Int
det (NG a1 a b1 b) = (fromIntegral (a1*b)) - (fromIntegral (a*b1))

lau :: NG -> [Natural] -> [NG]
lau m xs =  (map (foldl ingress m) (inits xs))

phi :: Double
phi = 0.5*(1 + sqrt 5)

test0 = ng_apply (NG 1 0 0 4) sqrt2
test1 = ng_apply (NG 2 1 0 2) (r2cf 13 11)
test2 = ng_apply (NG 1 0 1 2) (1 : tail e_constant)		-- (e-1)/(e+1)
