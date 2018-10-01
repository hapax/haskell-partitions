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