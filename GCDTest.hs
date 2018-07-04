import Data.List (foldl, genericLength, map)

sum' :: [Integer] -> Integer
sum' =  foldr (+) 0

a :: Integer
a =  2 ^ 40 

test :: Integer -> String
test b = 
       concat 
       ["a = ",      shows a "  a' = ",  shows a' "\n",
        "length = ", shows l "\n", 
        "gsSum = ",  shows gsSum "\n"
       ]
       where
       a'    = a - b
       gs    = [gcd a x | x <- [a' .. a]]
       l     = genericLength gs
       gsSum = sum' gs

b :: Integer
b =  2 ^ 25
   -- 1 0000 0000

main = putStrLn (test b)



