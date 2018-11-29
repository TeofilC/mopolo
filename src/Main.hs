{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
module Main where
import Control.Monad
import Control.Applicative hiding (empty)
import Data.List hiding (and)
import Data.Maybe
import Data.Bits

data Sentence = Let String
              | Cond Sentence Sentence
              | Neg  Sentence
              | Nec  Sentence
  deriving Eq

instance Show Sentence where
  show (Let s)= s
  show (Neg (Nec (Neg x))) = "@" ++ show x
  show (Neg x) = "~" ++ show x
  show (Cond (Neg x) y) = "(" ++ show x ++ "u" ++ show y ++ ")"
  show (Cond x y) = "("++ show x ++ "->" ++ show y ++ ")"
  show (Nec x) = "#" ++ show x

instance Bits Sentence where
  (.|.) x y  = Neg x --> y
  (.&.) x y = Neg (Neg x .|. Neg y)
  xor x y = Neg (x --> y .&. y --> x)
  complement = Neg
  isSigned _ = False
  bitSize _ = 1
  bit 0 = p .|. Neg p
  bit 1 = p .&. Neg p

data Model = Model
  { worlds :: Int
  , sees :: [(Int, Int)]
  , props :: [(Int, [Sentence])]
  , trans :: Bool
  , symm  :: Bool
  , ref   :: Bool
  }
  deriving Show

type Rule = ([Sentence], Sentence)

empty :: Model
empty = Model 1 [] [(0,[])] False False False

k,t,d,b,s4,s5 :: Model
k = empty
t = empty{sees = [(0,0)], ref = True}
d = undefined
b = t{symm = True}
s4 = t{trans = True}
s5 = t{trans = True, symm = True}

p,q,r :: Sentence
p = Let "P"
q = Let "Q"
r = Let "R"

pos, nec, no :: Sentence -> Sentence
pos x = Neg (Nec (Neg x))
nec = Nec
no  = Neg

(-->) :: Sentence -> Sentence -> Sentence
p --> q = Cond p q


fresh :: Model -> (Int, Model)
fresh m@Model{..} = (w, m { worlds = w + 1
                          , props = (w, []):props})
  where
    w = worlds

check :: Int -> Sentence -> Model -> Bool
check w x Model{..} = x `elem` fromJust (lookup w props)

add :: Int -> Sentence -> [(Int, [Sentence])] -> [(Int, [Sentence])]
add w x = map (\(w', ps) -> if w' == w then (w', nub (x:ps)) else (w', ps))

link :: Int -> Int -> Model -> Model
link x y m@Model{..} = m{
  sees = fix $ (x,y):sees
                        }
  where
    fix = fixT . fixS . fixR
    fixT s = if trans then
               nub $ [(x,z) | (x,y1) <-s, (y2,z) <- s, y1 == y2] ++ s
      else
               s
    fixS s = if symm then
               nub $ [(y,x) | (x,y) <- s] ++ s
      else
               s
    fixR s = if ref then
               nub $ [(x,x) | x <- [0..worlds-1]] ++ s
      else
               s

trickleUp :: Int -> Model -> [Model]
trickleUp w m@Model{..} = do
  foldM (\m x -> sat x w m) m (accesses >>= necessities)
  where
    accesses = map fst $ filter (\(x,y) -> y == w) sees
    necessities w = (\(Nec x) -> x) <$> filter (\case {Nec _ -> True; _ -> False}) (fromJust $ lookup w props)

theorem :: Sentence -> Model -> [Model]
theorem = flip sat 0

sat :: Sentence -> Int -> Model -> [Model]
sat l@(Let _) w m@Model{..} = do
  guard $ not $ check w (Neg l) m -- make sure ~Phi is not true
  pure $ m{
    props = add w l props
   }

sat (Neg l@(Let _)) w m@Model{..} = do
  guard $ not $ check w l m -- make sure Phi is not true
  pure $ m{
    props = add w (Neg l) props
   }

sat (Cond x y) w m@Model{..} = ant ++ conseq
  where ant = sat (Neg x) w m -- Either the antecedent is false
        conseq = sat y w m  -- Or the consequent is true

sat (Neg (Cond x y)) w m@Model{..} = sat x w m  >>= sat (Neg y) w -- x -> y is false iff x and not y is true

sat (Neg (Nec x)) w m = do
  let (w', m') = fresh m
  let m'' = link w w' m'
  trickleUp w' m'' >>= sat (Neg x) w'

sat (Nec x) w m = do
  guard $ not $ check w (Neg (Nec x)) m -- make sure ~[]Phi is not true
  let m' = m{
    props = add w (Nec x) (props m)
   }
  foldM (flip $ sat x) m' (filter (\x -> (w,x) `elem` sees m') [0..worlds m'])

sat (Neg (Neg x)) w m = sat x w m


main :: IO ()
main = do
  putStrLn "hello world"
