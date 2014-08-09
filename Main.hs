{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}
{-#  OPTIONS_GHC -XOverloadedStrings  #-}


module Main ( main )
where

import System.IO
import Data.List.Split (splitOn)
import Data.String
import Codec.TPTP 
import Control.Monad.Identity
import Data.List

-- File name containing the E proof
--fileName = "./Tests/Comm.txt" 
--fileName = "./Tests/refl.txt" 
--fileName = "./Tests/PropositionalFunction3.txt" 
--fileName = "./Tests/VariousArguments.txt" 
--fileName = "./Tests/Where3-43-A0.txt" 
--fileName = "./Tests/Where3-46-is.txt"
fileName = "./Tests/ImplicitArguments.txt"
--fileName = "/home/jis/fotc/snapshot-fot/DistributiveLaws/TaskB-AllStepsATP/124-j1.tptp"

main = do

  content <- parseFile fileName
  toAgda content
  --putStr (prettySimple content)
--  toName content
  return ()

-- Translates a list of TPTP Input into an string representation in Agda.
--  Need to verify the Agda Syntax!!
toAgda :: [TPTP_Input] -> IO [()]
toAgda = mapM (printLine . getString) 



-- Need to work on getting the annotations
getString :: TPTP_Input -> String 
getString input = (showF . getF . formula) input  ++ " --(" ++ (unrole . role) input ++ ")"  ++ " (" ++ showAW ( name input) ++ ")" ++ " Annotations: " ++ (getAnnotations . annotations) input


-- Helper functions to decompose the entries into specific terms. The term is indicated by the function name. E.g: toName extracts the name of the formula or term
toRole :: [TPTP_Input] -> IO [()]
toRole input = mapM (printLine . unrole . role ) input

toName :: [TPTP_Input] -> IO[()]
toName input = mapM (printLine . show . name) input

toComment :: [TPTP_Input] -> IO [()]
toComment  = mapM (printLine . show ) 

toAnnotations :: [TPTP_Input] -> IO [()]
toAnnotations = mapM ( printLine . getAnnotations . annotations )

getAnnotations :: Annotations -> String
getAnnotations (NoAnnotations) = "No anotations"
getAnnotations (Annotations gt ui) = getGeneralTerm gt ++ " " ++ getUsefulInfo ui

getGeneralTerm :: GTerm -> String
getGeneralTerm (ColonSep gd gt)= getGeneralTerm gt
getGeneralTerm (GTerm gd) = getGData gd
getGeneralTerm (GList gts) = unwords $ map getGeneralTerm gts

getGData :: GData -> String
getGData (GWord aw) = showAW aw
getGData (GApp aw gts) = showAW aw ++ "," ++ unwords ( map getGeneralTerm gts)
getGData (GVar v) = show v
getData (GNumber n) = show n
getData (GDistinctObject o) = show o
getData (GFormulaData s f) = show s ++ showF ( getF f)

getUsefulInfo :: UsefulInfo  -> String
getUsefulInfo (NoUsefulInfo) = "No useful info"
getUsefulInfo (UsefulInfo gs) = intercalate ","  $ map  show gs

getPredApp :: Formula0 (T Identity) (F Identity) -> [AtomicWord]
getPredApp (PredApp aw ts) = [aw]
getPredApp (BinOp f1 op f2) = getPredApp (getF f1) ++ getPredApp(getF f2)
--getPredApp (InfixPred t1 pred t2) = t1

getTerms ::  Formula0 (T Identity) (F Identity) -> [Term]
getTerms (PredApp aw ts) =  ts
getTerms (InfixPred t1 pred t2) = [ t1] ++ [t2]
getTerms (Quant quat v f) = getTerms ( getF f)
getTerms ((:~:) f) = getTerms (getF f)
getTerms (BinOp f1 op f2) = getTerms (getF f1) ++ getTerms (getF f2)

           
getBinOps :: Formula0 (T Identity) (F Identity)  -> [BinOp]
getBinOps (PredApp aw ts) = []
getBinOps (InfixPred t1 pred_ t2) = []
getBinOps (Quant quant v f) = []
getBinOps ((:~:) f) = [] -- [(:~:)] -- ++ getBinOps2 (runIdentity $ runF f)
getBinOps (BinOp f1 op f2) = [op]   ++ getBinOps ( getF f1 )   ++ getBinOps (getF f2)
         

reWriteBinOps :: [BinOp] -> [String]
reWriteBinOps [] = []
reWriteBinOps (x:xs) =  [rw x] ++ reWriteBinOps xs
                    

data AgdaSymbol = String
                deriving (Show)


-- Rewrites the binary operators to agda representation                         
rw :: BinOp -> String
rw (:|:) =  " ∨ "
rw (:=>:) = " ⇒ "
rw (:&:) = " ∧ "
rw (:~&:) = " ¬∧ "
rw (:<~>:) = " XOR "    
rw (:<=>:) = " ≡ "
rw (:<=:) = " ← "   

showFormula = showF . getF


showF :: Formula0 (T Identity) (F Identity) -> String
showF (BinOp f1 op f2) = "(" ++ showF (getF f1) ++  (rw (op))  ++ showF (getF f2) ++ ")"
showF (InfixPred t1 pred t2) = showT  (getT t1) ++ showP pred ++ showT (getT t2)
showF (Quant quant vs f) = quantToAgda quant vs  ++  showFormula f 
showF ((:~:) f) = "¬(" ++ showF (getF f) ++ ")"
showF (PredApp aw ts) =  showAW aw  ++  pStr  ( "(" ++  intercalate "," ( map (showT. getT) ts) ++ ")" ) 


pStr :: String -> String 
pStr str = 
    case str of
      [] -> "empty"
      (x:xs) -> if length str > 2 then str else []
  

filterBool :: String -> String
filterBool str | str == "$false" = "false"
               | str == "$true" = "true"
               | otherwise = str 


showP :: InfixPred -> String
showP (:=:) = " = "
showP (:!=:) = " ≠ "


showT:: Term0 (T Identity) -> String
showT (Var v) =  showV v
showT (NumberLitTerm r) =  show r
showT (DistinctObjectTerm o) =  show o
showT (FunApp aw ts) = showAW  aw ++  pStr ( "("++  intercalate ","  (map (showT . getT) ts)  ++ ")")


--showTs :: [Term0 term] -> [String]
showTs [] = []
showTs [t] = showT t
showTS (t:ts) = "showT" --  ++  showT t ++ showTs ts
   

showV :: V -> String
showV v =  removeWord (filter ( /= '"') $ show v) "V"

showVs :: [V] -> [String]
showVs [] = []
showVs (v:vs) =[ showV v] ++ showVs (vs)


quantToAgda :: Quant -> [V] -> String
quantToAgda Exists vs = "∃"  ++  intercalate ","  ( map showV vs) ++ " "
quantToAgda All vs = "∀" ++   intercalate ","  (map showV vs) ++" "


showAW ::AtomicWord -> String
showAW aw  = filterBool $   removeWord (rwAW aw) "AtomicWord" 

removeWord :: String -> String -> String
removeWord s w = unwords $ removeWord2 (words s) w


removeWord2 :: [String] -> String -> [String]
removeWord2 [] _ = []
removeWord2 (x:xs) w | (x == w) = removeWord2 xs w
removeWord2 (x:xs) w = [x] ++ removeWord2 xs w


rwAW :: AtomicWord -> String
rwAW aw = filter ( /= '"')  $  show  aw                               


getT = runIdentity . runT

getF = runIdentity . runF 

--getBinOpsF :: F Identity -> [BinOp]
getBinOpsF f = runF f

getRun f = case f  of   
              F g -> runF f 
              --BinOp t1 op t2 -> op
              --Identity h -> i
              --BinOp t1 op t2 -> 3

printLine :: String -> IO ()
printLine  = putStrLn 

getFormula list index = formula $  (list !! index)

countLines :: [String] → Int
countLines list = length list


cleanFile :: [String] -> [String]
cleanFile = removeHaskellComments . removeEmptyLines 


-- Removes haskell line comments which start with '#'
removeHaskellComments :: [String] -> [String]
removeHaskellComments file = removeComments file '#'

--Removes the comment lines 
removeComments :: [String] -> Char -> [String]
removeComments file commentChar =  filter (\line -> (head line) /= commentChar) file

-- Removes the blank spaces in the text
removeEmptyLines :: [String] -> [String]
removeEmptyLines  = filter (not . null)


-- split a string using ',' as delimeter
splitLines :: String ->  [String]
splitLines  = splitOn ","  

--Order of processing
-- 1. Scape characters
-- 2. Remove comment lines
-- 3. Parse structure
-- 4. Define Data structure

data TPTP = TPTP { clauseType :: String
                 , numberLine :: String
                 , expression :: String
                 } deriving (Show)


type NumberLine = String
type Type = String
type Expression = String



--
-- 1. Separate the formula components
