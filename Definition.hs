module Definition where

data BS a = Yes a | No a
 deriving Show

{- ESTADO -}
type State = String 

type Transition = String

type S = [State]
type N = [Transition]
type T = [State]
type R = [(State,Transition,State)]

type LTS = (S,N,T,R)

type BisimulationRelation = [(State,State)]