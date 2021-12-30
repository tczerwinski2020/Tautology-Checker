-- Taylor Czerwinski
-- CSE 4250
-- Tautology Checker

import System.IO( isEOF )
import Data.List
import Data.Maybe (fromJust)
main :: IO()

isOperand :: Char -> Bool
isOperand x = if x == 'A' || x == 'C' || x == 'D' || x == 'E' || x== 'J' || x== 'K' || x == 'N'
   then True
   else False

nextParen :: String -> Int -> Int -> Int -> Int
nextParen expression position lCount rCount
  | equal = position - 1
  | position == length expression = -1
  | (expression !! position) == ')' = nextParen expression (position + 1) lCount newR
  | (expression !! position) == '(' = nextParen expression (position + 1) newL rCount
  | otherwise = nextParen expression (position + 1) lCount rCount
  where
    equal = (not (lCount == 0)) && (lCount == rCount)
    newR = rCount + 1
    newL = lCount + 1

toInFix :: String -> [String] -> Int -> String
toInFix line stack position
  | position == length line  = lastVar
  | notOp  = toInFix line updatedStack (position + 1)
  | otherwise = toInFix line thirdStack (position + 1)
  where
    newStack = take ((length stack) - 1) stack
    lastVar = last stack
    curr = line !! position
    notOp = not (isOperand curr)
    updatedStack = stack ++ [[curr]]
    operator1 = stack !! ((length stack) - 1)
    operator2 = stack !! ((length stack) - 2)
    temp = take ((length stack) - 2) stack
    str = "(" ++ operator2 ++ [curr] ++ operator1 ++ ")"
    thirdStack = temp ++ [str]

type Atom = Char 

data Formula = Atom String
 | Not Formula
 | And Formula Formula
 | Or Formula Formula

showFormula :: Formula -> String
showFormula (Atom name) = name
showFormula (Not f1) = "~"++ showFormula f1 ++""
showFormula (And a b) = "("++(showFormula a) ++ " & " ++ showFormula b++")"
showFormula (Or a b) = "(" ++ (showFormula a) ++ " v " ++ showFormula b ++ ")"

getNextOp :: String -> Int
getNextOp expression 
 | expression !! 0 == '(' = a
 | otherwise = 1
  where
  endA = nextParen expression 0 0 0
  a = if endA == -1 then 1 else endA+1


getFormula :: String -> Int -> Formula 
getFormula expression position
 | position == length expression = Atom ""
 | length expression == 1 && notParen = Atom [(expression !! position)]
 | expression !! position == 'N' = notexp
 | expression !! nextOp == 'K' = andexp
 | expression !! nextOp == 'A' = orexp
 | expression !! nextOp == 'C' = cExp
 | expression !! nextOp == 'D' = dExp
 | expression !! nextOp == 'E' = eExp
 | expression !! nextOp == 'J' = jExp
 | otherwise = getFormula expression (position+1)
  where 
  notexp = Not (getFormula (f1) 0)
  nextP = nextParen expression (position +1) 0 0
  end = if nextP == -1 then (length expression)-1 else nextP
  f1 = drop (position+2) (take end expression)
  nextOp = getNextOp (drop position expression)
  andexp = And formA formB
  a = if nextOp == (position + 1) then [expression !! position] else drop (position+1) (take (nextOp-1) expression)
  alpha = nextParen expression (position) 0 0
  beta = nextParen expression (nextOp+1) 0 0
  b = if beta == -1 then [expression !! (nextOp + 1)] else drop (nextOp + 2) (take (beta) expression)
  formA = getFormula a 0
  formB = getFormula b 0 
  notParen = not ((expression !! position) == ')') && not ((expression !! position) == '(')
  orexp = Or (getFormula a 0) (getFormula b 0)

  cExp = Or (Not(getFormula a 0)) (getFormula b 0)
  dExp = Not (And (getFormula a 0) (getFormula b 0))
  eExp = And (cExp) (Or (Not (getFormula b 0)) (getFormula a 0)) 
  firstJ = And (getFormula a 0) (Not (getFormula b 0))
  secondJ = And (Not (getFormula a 0)) (getFormula b 0)
  jExp = Or firstJ secondJ

toNNF :: Formula -> Formula 
toNNF (Atom p) = Atom p
toNNF (Not (Not p)) = (toNNF p)
toNNF (And p q) = And (toNNF p) (toNNF q)
toNNF (Or p q) = Or (toNNF p) (toNNF q)
toNNF (Not (And p q)) = Or (toNNF $ Not p) (toNNF $ Not q)
toNNF (Not (Or p q)) = And (toNNF $ Not p) (toNNF $ Not q)
toNNF (Not p) = Not $ toNNF p
        
toCNF :: Formula -> Formula 
toCNF formula = case formula of 
  Or p q -> distribute (toCNF p) (toCNF q)
  And p q -> And (toCNF p) (toCNF q)
  (_) -> formula 

distribute :: Formula -> Formula -> Formula 
distribute x y = case (x, y) of 
 (And p q, y) -> And (distribute p y) (distribute q y)
 (x, And p q) -> And (distribute x p) (distribute x q)
 (x,y) -> Or x y

eval :: Formula -> [(String, Bool)] -> Bool 
eval (Atom a) bs = fromJust (lookup a bs)
eval (Not a) bs = not (eval a bs)
eval (And a b) bs = (eval a bs) && (eval b bs)
eval (Or a b) bs = (eval a bs) || (eval b bs)

vars :: Formula -> [String]
vars (Atom v) = [v]
vars (Not f1) = vars f1
vars (And f1 f2) = vars f1 ++ vars f2
vars (Or f1 f2) = vars f1 ++ vars f2

listVar :: Formula -> [String]
listVar = nub . vars

bools = [True, False]

boolTable :: [String] -> [[(String, Bool)]]
boolTable [] = [[]]
boolTable (a: as) = [(a,b) : r | b <- bools, r <- boolTable as]

truthTable :: Formula -> [([(String, Bool)], Bool)]
truthTable e = [(bs, eval e bs) | bs <- boolTable (listVar e)]

allTrue :: [Bool] -> String
allTrue (a) = if (False `elem` a) then "false" else "true"


main = do
 let stack = []
 done <- isEOF 
 if done
   then return()
 else do
  line <- getLine
  let inFix = toInFix line stack 0 
  let dropParen = drop 1 (take ((length inFix)-1) inFix)
  let formula = getFormula dropParen 0
  let nnf = toNNF formula
  let cnf = toCNF nnf
  let (xs, ys) = unzip (truthTable cnf)
  putStrLn $ allTrue ys ++ " " ++ showFormula cnf
  main

