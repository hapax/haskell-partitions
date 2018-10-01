-- Program to search for partition identities
-- David Wakeham, Aug 14 2015

{-- BASIC IDEA

Want to construct subset S ≤ N such that partitions of
n with elements in S, p(S, n), equal the number of
partitions of n with some property, D(n). The function
D is given and we want to find S.
--}

module HaskPart where
import Data.List

-- Recursively generate partitions

indexedAdd :: ([Int], Int) -> [Int]
indexedAdd (x:xs, 1) = (x+1):xs
indexedAdd (x:xs, n) = x:(indexedAdd (xs, (n-1)))

addOne :: [Int] -> [[Int]]
addOne ls = map indexedAdd zipped
           where numCopies = length ls
                 copyLs    = replicate numCopies ls
                 zipped    = zip copyLs [1..numCopies]

partitions :: Int -> [[Int]]
partitions 0 = [[]]
partitions n = nub $ biggerParts ++ newParts
           where recurParts  = partitions (n-1)
                 newParts    = [ [1] ++ part | part <- recurParts ]
                 biggerParts = map sort $ concat $ map addOne recurParts

-- Partitions with allowed/forbidden elements

supersetOf :: [Int] -> [Int] -> Bool
supersetOf sup = foldl (\t x -> and [x `elem` sup, t]) True

forbiddenNums :: [Int] -> [Int] -> Bool
forbiddenNums forbidList = foldl (\t x -> and [not $ x `elem` forbidList, t]) True

remainders :: Int -> [Int] -> [Int]
remainders b [] = [1..]
remainders b rs = filter correctRem [1..]
           where correctRem num = (rem num b) `elem` rs

-- Other properties of partitions

differsBy :: Int -> [Int] -> Bool
differsBy _ []   = True
differsBy n ls = all (>=n) diffs
          where diffs  = zipWith (-) (tail ls) ls

biggerThan :: Int -> [Int] -> Bool
biggerThan n = all (>n)

lessThan :: Int -> [Int] -> Bool
lessThan n = all (<n)

limitReps :: Int -> [Int] -> Bool
limitReps n ls = all (<=n) repLengths
          where repLengths = map length $ group ls

noConsecMult :: Int -> [Int] -> [Int] -> Bool
noConsecMult b rs ls = all test pairDiffs
          where diffs     = zipWith (-) (tail ls) ls
                pairDiffs = zip diffs $ tail ls
                test      = \(x, y) -> or [ x /= b, not $ (rem y b) `elem` rs]

predGaps :: Int -> [Int] -> Int -> [Int] -> Bool
predGaps b rs gap ls = all test pairDiffs
          where diffs     = zipWith (-) (tail ls) ls
                pairDiffs = zip diffs $ tail ls
                test      = \(x, y) -> or [ x > gap, not $ (rem y b) `elem` rs]

predGap :: Int -> Int -> Int -> [Int] -> Bool
predGap b r gap ls = all test pairDiffs
          where diffs     = zipWith (-) (tail ls) ls
                pairDiffs = zip diffs $ tail ls
                test     = \(x, y) -> or [ x > gap, r /= rem y b]

noConsecMults :: Int -> Int -> [Int] -> Bool
noConsecMults b r ls = all test pairDiffs
          where diffs     = zipWith (-) (tail ls) ls
                pairDiffs = zip diffs $ tail ls
                test      = \(x, y) -> or [ x /= b, r /= rem y b]

-- Logically combine predicates

andPreds :: [[Int] -> Bool] -> [Int] -> Bool
andPreds predLs part = and $ map ($ part) predLs

orPreds :: [[Int] -> Bool] -> [Int] -> Bool
orPreds predLs part = or $ map ($ part) predLs

-- UNFINISHED - need to work out how to generate list

combinePred :: (Bool -> Bool -> Bool) -> [[Int] -> Bool] -> [Int] -> Bool
combinePred predLs part = and $ map ($ part) predLs

-- Iteratively construct S if it exists, otherwise produce error

numPartsPred :: ([Int] -> Bool) -> Int -> Int
numPartsPred partPred n = length $ filter partPred $ partitions n

buildSetStep :: ([Int] -> Bool) -> [Int] -> Int -> [Int]
buildSetStep partPred setSoFar current
                      | numPartsPred partPred current == numPartsPred setSoFarPred current = setSoFar
                      | numPartsPred partPred current == numPartsPred setAddPred current   = setAdd
                      | otherwise                                                          = error "no set"
                      where setAdd       = setSoFar ++ [current]
                            setSoFarPred = supersetOf setSoFar
                            setAddPred   = supersetOf setAdd

buildSet :: ([Int] -> Bool) -> Int -> [Int]
buildSet partPred maxNumber = foldl step [] [1..maxNumber]
         where step = buildSetStep partPred

-- Pentagonal stuff for p(n)

pentagonal :: Int -> Int
pentagonal n = quot (3*n*n - n) 2

pentagonInv :: Int -> Int
pentagonInv g = round root
            where float = fromIntegral g
                  root  = (/6) . (+1) . sqrt $ (24*float + 1)

-- Predicates to check (labelling from Number Theory, George Andrews)

d1 = differsBy 1
-- [1,3,5,7,9,11,13,15,17,19,..]
-- Guess: odd numbers

d2 = differsBy 2
-- [1,4,6,9,11,14,16,19,21,24,..]
-- Guess: natural numbers equal to 1, 4 mod 5

d3 = differsBy 3
-- **Exception: no set

e1 = combinePreds [noConsecMults 2 0, differsBy 2]
-- [1,4,7,9,12,15,17,20,23,25,..]
-- Guess: natural numbers equal to 1, 4, 7 mod 8

e2 = combinePreds [noConsecMults 2 1, differsBy 2]
-- [1,5,6,9,13,14,17,21,22,25,..]
-- Guess: natural number equal to 1, 5, 6 mod 8

e3 = combinePreds [noConsecMults 2 0, differsBy 2, biggerThan 2]
-- [3,4,5,11,12,13,19,20,21,..]
-- Guess: natural numbers equal to 3, 4, 5 mod 8

e4 = combinePreds [noConsecMults 2 1, differsBy 2, biggerThan 1]
-- [2,3,7,10,11,15,18,19,23,..]
-- Guess: natural numbers equal to 2, 3, 7 mod 8

e5 = limitReps 2
-- [1,2,4,5,7,8,10,11,13,14,16,17,19,20,22,23,25,..]
-- Guess: no multiples of 3

e6 = combinePreds [predGap 2 1 2, biggerThan 1]
-- [2,3,4,7,8,10,11,12,15,16,18,19,20,23,24,..]
-- Guess: nothing equal to 1 mod 4