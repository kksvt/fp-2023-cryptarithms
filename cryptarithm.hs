--Cryptarithms
import System.IO
import System.Environment

isLetter :: Char -> Bool
--isLetter x = (x >= 'a' && x <= 'z') || (x >= 'A' && x <= 'Z')
isLetter x = x >= 'A' && x <= 'Z' --only capital letters are valid variables

splitInput :: (Char -> Bool) -> String -> (String, String)
splitInput _ [] = ([], [])
splitInput f xs = splitInputAux f xs []
 where splitInputAux f [] moved = ([], reverse moved)
       splitInputAux f (y:ys) moved = if f y then splitInputAux f (ys) (y:moved) else (y:ys, reverse moved) 

--marked element, number of marked elements
data MyStack a = MyStackR [a] a Int

mypop :: (Eq a) => MyStack a -> MyStack a
mypop (MyStackR [] _ _) = error "Attempted to pop an empty stack!"
mypop (MyStackR (x:xs) marked n) = if marked == x then MyStackR xs marked (n-1) else MyStackR xs marked n 

mypush :: (Eq a) => MyStack a -> a -> MyStack a
mypush (MyStackR xs marked n) e = if marked == e then MyStackR (e:xs) marked (n+1) else MyStackR (e:xs) marked n

myisempty :: MyStack a -> Bool
myisempty (MyStackR [] _ _) = True
myisempty _ = False

getmarked :: MyStack a -> Int
getmarked (MyStackR _ _ n) = n

ms2list :: MyStack a -> [a]
ms2list (MyStackR xs _ _) = xs

--subsequences, permutations
subsequences :: [a] -> [[a]]
subsequences xs = concat (foldr subsequencesAux [[[]]] xs)
 where subsequencesAux y ys = zipWith (\v1 v2 -> (map (y:) v1) ++ v2) ([]:ys) (ys ++ [[]])

permutations :: (Eq a) => [a] -> [[a]]
permutations [] = [[]]
permutations xs = [e:x | e <- xs, x <- (permutations (filter (\x -> e /= x) xs))]

--operator utils
operatorPriority :: Char -> Int
operatorPriority '*' = 2
operatorPriority '/' = 2
operatorPriority '+' = 1
operatorPriority '-' = 1
operatorPriority _ = 0

operatorValid :: Char -> Bool
operatorValid '+' = True
operatorValid '*' = True
operatorValid '/' = True
operatorValid '-' = True
operatorValid '=' = True
operatorValid _ = False

roughen xs = foldl (\acc elem -> [elem] : acc) [] (reverse xs)

--input, stack, output
infixToRPN :: String -> MyStack Char -> [String]
infixToRPN [] stack = roughen (ms2list stack)
infixToRPN (' ':xs) stack = infixToRPN xs stack
infixToRPN ('(':xs) stack = infixToRPN xs (mypush stack '(')
infixToRPN (x:xs) stack
 | x == ')' = if getmarked stack == 0 then error "Unpaired closing bracket" else (roughen stackUntilBracket) ++ (infixToRPN xs (MyStackR stackRemainderBracket markedElement (numMarkedElements - 1)))
 | operatorValid x = if operators == [] then infixToRPN xs (MyStackR (x:stackRemainder) markedElement numMarkedElements) else (roughen operators) ++ (infixToRPN xs (MyStackR (x:stackRemainder) markedElement numMarkedElements))
 | isLetter x = letters : (infixToRPN remainingInput stack)
 | otherwise = error ("Invalid character " ++ [x])
 where (remainingInput, letters) = splitInput (isLetter) (x:xs)
       (stackRemainder, operators) = splitInput (\y -> operatorPriority x < operatorPriority y) stacklist
       ('(':stackRemainderBracket, stackUntilBracket) = splitInput (\y -> y /= '(') stacklist
       (MyStackR stacklist markedElement numMarkedElements) = stack

removeVarDups :: [(Char, Bool)] -> [(Char, Bool)]
removeVarDups [] = []
removeVarDups (x:xs)
 | overwriteVar x xs = removeVarDups xs
 | otherwise = x : (removeVarDups (filter (\z -> fst x /= fst z) xs))
 where overwriteVar _ [] = False
       overwriteVar v (y:ys) = if (fst v == fst y && (snd v == snd y || snd y == True)) then True else overwriteVar v ys 

getAllVars :: [String] -> ([(Char, Bool)], Int)
getAllVars xs = if len > 10 then error "The number of distinct variables exceeds 10" else (variableSet, len)
 where variableSet = removeVarDups pairList
       len = length variableSet
       pairList = foldr (\var acc -> if (operatorValid (head var)) then acc else (parseAsPair True var) ++ acc) [] xs
       parseAsPair _ [] = []
       parseAsPair _ (y:[]) = [(y, False)]
       parseAsPair isFirst (y:ys) = (y, isFirst) : (parseAsPair False ys)

--evaluates an RPN expression
--all the operators we deal with take in 2 arguments
--input, stored vars, is equal
data RPNField = RPNValue Integer | RPNOperator Char deriving Show

evaluateExpression :: [RPNField] -> [Integer] -> Bool
evaluateExpression ((RPNOperator '=') : []) (n:m:l:vars) = error "The expression is invalid. The stack holds 3 or more values."
evaluateExpression ((RPNOperator '=') : []) (n:m:[]) = n == m
evaluateExpression ((RPNOperator '=') : []) (n:[]) = error "The expression is invalid: The stack holds only one value."
evaluateExpression ((RPNOperator '=') : []) [] = error "The expression is invalid: The stack is empty."
evaluateExpression ((RPNOperator '=') : vars) _ = error "The expression is invalid: The equals sign is not the last operator on the stack."
evaluateExpression ((RPNOperator o) : xs) (n:m:vars) = evaluateExpression xs ((f o m n) : vars)
 where f '+' m n = m + n
       f '-' m n = m - n
       f '*' m n = m * n
       f '/' m n = m `div` n
evaluateExpression ((RPNValue v) : xs) vars = evaluateExpression xs (v : vars)
evaluateExpression _ _ = error "The expression is invalid."

varMapping :: Char -> [(Char, Char)] -> Char
varMapping x [] = error "No mapping found. This should never happen."
varMapping x (m:ms) = if x == (fst m) then snd m else varMapping x ms

evaluateCryptarithm :: [String] -> [(Char, Char)] -> Bool
evaluateCryptarithm xs ht = evaluateExpression properRPN []
 where termMapping s = map (\x -> varMapping x ht) s
       properRPN = map (\x -> if (operatorValid $ head x) then (RPNOperator (head x)) else (RPNValue (read (termMapping x) :: Integer))) xs

solve :: String -> [(Char, Char)]
solve input = solution allCombinations
 where rpn = infixToRPN input (MyStackR [] '(' 0)
       (vdata, numvars) = getAllVars rpn
       allCombinations = filter (\x -> (length x) == numvars) (subsequences "0123456789")
       validAssignment c = foldl (\acc elem -> ((fst elem) == False || (snd elem) /= '0') && acc) True (zip (map (\(x, y) -> y) vdata) c)
       iteratePermutations [] = [] 
       iteratePermutations (p:perm) = if validAssignment p then (if (evaluateCryptarithm rpn pMapped) then pMapped else iteratePermutations perm) else iteratePermutations perm where pMapped = (zip (map (\(x, y) -> x) vdata) p)
       solution [] = []
       solution (c:combs) = if (iteratePermutationsResult == []) then solution combs else iteratePermutationsResult where iteratePermutationsResult = iteratePermutations (permutations c)

translateSolution :: [(Char, Char)] -> String
translateSolution [] = ""
translateSolution (x:[]) = ((fst x):" = ") ++ [(snd x)]
translateSolution (x:xs) = ((fst x):" = ") ++ [(snd x)] ++ ", " ++ (translateSolution xs)

solveFileLine :: (String -> String) -> Handle -> IO ()
solveFileLine f input = do
 eof <- hIsEOF input
 if eof then do return()
 else do 
  x <- hGetLine input
  putStrLn ("Trying to solve " ++ x)
  putStrLn $ f x
  solveFileLine f input

readInputFile :: FilePath -> IO ()
readInputFile fname = do 
 input <- openFile fname ReadMode
 solveFileLine (translateSolution . solve) input

main :: IO ()
main = do
 fname <- getArgs
 readInputFile (head fname)