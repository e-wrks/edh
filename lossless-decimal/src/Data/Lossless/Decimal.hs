-- | a numeric type for lossless decimal arithmetic
module Data.Lossless.Decimal where

import Data.Char (chr, ord)
import Data.Hashable (Hashable (hashWithSalt))
import qualified Data.Scientific as Scientific
import GHC.Real
  ( denominator,
    numerator,
    (%),
    (^^%^^),
  )
import Prelude

data Decimal = Decimal
  { denominator'10 :: !Integer,
    exponent'10 :: !Integer,
    numerator'10 :: !Integer
  }

decimalToInteger :: Decimal -> Maybe Integer
decimalToInteger v
  | d /= 1 || e < 0 = Nothing
  | e == 0 = Just n
  | otherwise = Just $ n * 10 ^ e
  where
    Decimal d e n = normalizeDecimal v
{-# INLINE decimalToInteger #-}

-- | Use this with great sure, this even do NO normalization,
-- and will crash your process by throwing error if the cast
-- fails.
castDecimalToInteger :: Decimal -> Integer
castDecimalToInteger x@(Decimal d e n)
  | d /= 1 || e < 0 = error $ "not an integer: " ++ show x
  | e == 0 = n
  | otherwise = n * 10 ^ e
{-# INLINE castDecimalToInteger #-}

decimalFromScientific :: Scientific.Scientific -> Decimal
decimalFromScientific sn =
  Decimal
    1
    (fromIntegral $ Scientific.base10Exponent sn')
    (Scientific.coefficient sn')
  where
    sn' = Scientific.normalize sn

nan :: Decimal
nan = Decimal 0 0 0

inf :: Decimal
inf = Decimal 0 0 1

decimalIsNaN :: Decimal -> Bool
decimalIsNaN (Decimal d _e n) = d == 0 && n == 0

decimalIsInf :: Decimal -> Bool
decimalIsInf (Decimal d _e n) = d == 0 && n /= 0

normalizeInteger :: Integer -> Decimal
normalizeInteger i = Decimal d e $ if neg then - n else n
  where
    neg = i < 0
    p = abs i

    (p1, !c5) = countPrimeFactor 5 p
    (p2, !c2) = countPrimeFactor 2 p1

    (d, e, n)
      | c2 == c5 = (1, c2, p2)
      | c2 < c5 = (2 ^ (c5 - c2), c5, p2)
      | otherwise = (5 ^ (c2 - c5), c2, p2) -- c2 > c5

normalizeDecimal :: Decimal -> Decimal
normalizeDecimal (Decimal d e n)
  | d == 0 = Decimal 0 0 $ if n == 0 then 0 else if n < 0 then (-1) else 1
  | n == 0 = Decimal 1 0 0
  | otherwise = Decimal d'' e' $ if neg then - n'' else n''
  where
    neg = if n < 0 then d > 0 else d < 0
    pn = abs n
    pd = abs d

    (pn', n5) = countPrimeFactor 5 pn
    (pn'', n2) = countPrimeFactor 2 pn'

    (pd', d5) = countPrimeFactor 5 pd
    (pd'', d2) = countPrimeFactor 2 pd'

    (pn5, pd5)
      | n5 > d5 = (n5 - d5, 0)
      | otherwise = (0, d5 - n5)
    (pn2, pd2)
      | n2 > d2 = (n2 - d2, 0)
      | otherwise = (0, d2 - n2)

    (d', e', n')
      | pd'' == 1 =
        let (ea1, nm1, pd5', pd2') =
              if pn5 > pn2
                then (pn5, 1, pd5, pd2 + pn5 - pn2)
                else (pn2, 1, pd5 + pn2 - pn5, pd2)
            (ea2, nm2, dm) =
              if pd5' > pd2'
                then (- pd5', 2 ^ (pd5' - pd2'), 1)
                else (- pd2', 5 ^ (pd2' - pd5'), 1)
         in (pd'' * dm, e + ea1 + ea2, pn'' * nm1 * nm2)
      | otherwise =
        let (ea1, nm) =
              if pn5 > pn2
                then (pn2, 5 ^ (pn5 - pn2))
                else (pn5, 2 ^ (pn2 - pn5))
            (ea2, dm) =
              if pd5 > pd2
                then (- pd2, 5 ^ (pd5 - pd2))
                else (- pd5, 2 ^ (pd2 - pd5))
         in (pd'' * dm, e + ea1 + ea2, pn'' * nm)

    (n'', d'') = simplify n' d'

    simplify :: Integer -> Integer -> (Integer, Integer)
    simplify x y
      | x == 0 || y == 0 = (x, y)
      | cd <= 1 = (x, y)
      | otherwise = (x `div` cd, y `div` cd)
      where
        cd = gcd x y

instance Show Decimal where
  show = showDecimal

-- | neither x nor y can be nan, but not checked
compareNonNanDecimal :: Decimal -> Decimal -> Ordering
compareNonNanDecimal (Decimal x'd x'e x'n) (Decimal y'd y'e y'n)
  | -- both are inf, but may be different sign
    x'd == 0 && y'd == 0 =
    compare (signum x'n) (signum y'n)
  | otherwise =
    if x'e >= y'e
      then compare (x'n * y'd * 10 ^ (x'e - y'e)) (y'n * x'd)
      else compare (x'n * y'd) (y'n * x'd * 10 ^ (y'e - x'e))

instance Ord Decimal where
  compare x@(Decimal x'd _x'e x'n) y@(Decimal y'd _y'e y'n)
    | x'd == 0 && x'n == 0 = if y'd == 0 && y'n == 0 then EQ else GT
    | y'd == 0 && y'n == 0 = LT
    | otherwise = compareNonNanDecimal x y

instance Eq Decimal where
  x@(Decimal x'd _x'e x'n) == y@(Decimal y'd _y'e y'n)
    | -- either is nan
      (x'd == 0 && x'n == 0) || (y'd == 0 && y'n == 0) =
      False
    | otherwise = EQ == compareNonNanDecimal x y

instance Hashable Decimal where
  hashWithSalt s (Decimal d e n) =
    s `hashWithSalt` d `hashWithSalt` e `hashWithSalt` n

instance Num Decimal where
  fromInteger = normalizeInteger
  (+) = addDecimal
  (*) = mulDecimal
  abs (Decimal d e n) = Decimal (abs d) e (abs n)
  signum (Decimal d _e n) = Decimal 1 0 $ signum n * signum d
  negate = negateDecimal

instance Real Decimal where
  toRational (Decimal d e n) =
    if e < 0 then n % (d * 10 ^ (- e)) else (n * 10 ^ e) % d

instance Fractional Decimal where
  fromRational x = normalizeDecimal $ Decimal (denominator x) 0 (numerator x)
  (/) = divDecimal

decimalGreater :: Decimal -> Decimal -> Bool
decimalGreater x@(Decimal x'd _x'e x'n) y@(Decimal y'd _y'e y'n)
  | -- always False when nan involved
    (x'd == 0 && x'n == 0) || (y'd == 0 && y'n == 0) =
    False
  | otherwise = GT == compareNonNanDecimal x y

decimalGreaterOrEq :: Decimal -> Decimal -> Bool
decimalGreaterOrEq x@(Decimal x'd _x'e x'n) y@(Decimal y'd _y'e y'n)
  | -- always False when nan involved
    (x'd == 0 && x'n == 0) || (y'd == 0 && y'n == 0) =
    False
  | otherwise = LT /= compareNonNanDecimal x y

decimalLess :: Decimal -> Decimal -> Bool
decimalLess x@(Decimal x'd _x'e x'n) y@(Decimal y'd _y'e y'n)
  | -- always False when nan involved
    (x'd == 0 && x'n == 0) || (y'd == 0 && y'n == 0) =
    False
  | otherwise = LT == compareNonNanDecimal x y

decimalLessOrEq :: Decimal -> Decimal -> Bool
decimalLessOrEq x@(Decimal x'd _x'e x'n) y@(Decimal y'd _y'e y'n)
  | -- always False when nan involved
    (x'd == 0 && x'n == 0) || (y'd == 0 && y'n == 0) =
    False
  | otherwise = GT /= compareNonNanDecimal x y

negateDecimal :: Decimal -> Decimal
negateDecimal (Decimal d e n) = Decimal d e (- n)

addDecimal :: Decimal -> Decimal -> Decimal
addDecimal (Decimal x'd x'e x'n) (Decimal y'd y'e y'n) =
  normalizeDecimal $
    if x'e >= y'e
      then Decimal (x'd * y'd) y'e (x'n * y'd * 10 ^ (x'e - y'e) + y'n * x'd)
      else Decimal (x'd * y'd) x'e (x'n * y'd + y'n * x'd * 10 ^ (y'e - x'e))

subsDecimal :: Decimal -> Decimal -> Decimal
subsDecimal x y = addDecimal x $ negateDecimal y

mulDecimal :: Decimal -> Decimal -> Decimal
mulDecimal (Decimal x'd x'e x'n) (Decimal y'd y'e y'n) =
  normalizeDecimal $ Decimal (x'd * y'd) (x'e + y'e) (x'n * y'n)

divDecimal :: Decimal -> Decimal -> Decimal
divDecimal (Decimal x'd x'e x'n) (Decimal y'd y'e y'n) =
  mulDecimal (Decimal x'd x'e x'n) (Decimal y'n (- y'e) y'd)

divIntDecimal :: Decimal -> Decimal -> Decimal
divIntDecimal x y = case decimalToInteger x of
  Nothing -> nan
  Just xi -> case decimalToInteger y of
    Nothing -> nan
    Just yi -> Decimal 1 0 $ xi `div` yi

modIntDecimal :: Decimal -> Decimal -> Decimal
modIntDecimal x y = case decimalToInteger x of
  Nothing -> nan
  Just xi -> case decimalToInteger y of
    Nothing -> nan
    Just yi -> Decimal 1 0 $ xi `mod` yi

powerDecimal :: Decimal -> Decimal -> Decimal
powerDecimal x y = case decimalToInteger y of
  Nothing -> nan -- todo should otherwise support this case?
  Just y'i -> fromRational $ toRational x ^^%^^ y'i

showDecimal :: Decimal -> String
showDecimal v
  | d == 0 = if n == 0 then "nan" else if n < 0 then "-inf" else "inf"
  | d == 1 = showDecInt n e
  | d == (-1) = showDecInt (- n) e
  | e < 0 = showDecInt n 0 ++ "/" ++ showDecInt d (- e)
  | otherwise = showDecInt n e ++ "/" ++ showDecInt d 0
  where
    Decimal d e n = normalizeDecimal v
    showDecInt :: Integer -> Integer -> String
    showDecInt n_ e_ =
      if n_ < 0 then '-' : positiveInt (- n_) e_ else positiveInt n_ e_
    positiveInt :: Integer -> Integer -> String
    positiveInt n_ e_
      | n_ >= 0 = case encodeInt n_ 0 "" of
        (0, _) -> "0"
        (l, s@(d1 : ds)) ->
          let ee = e_ + fromIntegral l - 1
              cmpcForm =
                if e_ >= 0
                  then -- append trailing zeros as necessary
                    s ++ replicate (fromInteger e_) '0'
                  else -- do left shifting of decimal point

                    let mid = fromIntegral l + e_
                     in ( if mid > 0
                            then -- place decimal point in middle

                              let (p1, p2) = splitAt (fromInteger mid) s
                               in p1 ++ "." ++ p2
                            else -- prepend leading zeros
                              "0." ++ replicate (- fromInteger mid) '0' ++ s
                        )
              normForm =
                d1 : fractPart ds ++ if ee == 0 then "" else "e" ++ straightInt ee
           in if abs ee < 5 then cmpcForm else normForm
        _ -> error "impossible case"
      | otherwise = error "bug"
    straightInt :: Integer -> String
    straightInt n_ = let (_l, s) = encodeInt n_ 0 "" in s
    encodeInt :: Integer -> Int -> String -> (Int, String)
    encodeInt n_ l buf
      | abs n_ < 10 =
        if n_ == 0
          then (l, buf)
          else
            if n_ < 0
              then (l + 2, '-' : digitChar (- n_) : buf)
              else (l + 1, digitChar n_ : buf)
      | otherwise =
        let (n', r) = n_ `quotRem` 10
         in encodeInt n' (l + 1) $ digitChar (abs r) : buf
    digitChar :: Integer -> Char
    digitChar n_
      | 0 <= n_ && n_ < 10 = chr $ ord '0' + (fromIntegral n_ :: Int)
      | otherwise = error "bug"
    trimTrailingZeros :: String -> String
    trimTrailingZeros = reverse . dropWhile (== '0') . reverse
    fractPart :: String -> String
    fractPart ds_ = case trimTrailingZeros ds_ of
      "" -> ""
      ds_' -> '.' : ds_'

countPrimeFactor :: Integer -> Integer -> (Integer, Integer)
countPrimeFactor _ 0 = (0, 0)
countPrimeFactor !f !i =
  let (q, r) = quotRem i f
   in case r of
        0 -> let (i', r') = countPrimeFactor f q in (i', r' + 1)
        _ -> (i, 0)
