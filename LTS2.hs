module BissimulationTest where

import Cp
import Definition
import Examples


infix 4 <=>
infix 4 +++
infix 4 <<


-- Projecçoes sobre LTS

pl1 :: (a,b,c,d) -> a
pl1 (a,_,_,_) = a

pl2 :: (a,b,c,d) -> b
pl2 (_,b,_,_) = b

pl3 :: (a,b,c,d) -> c
pl3 (_,_,c,_) = c
	
pl4 :: (a,b,c,d) -> d
pl4 (_,_,_,d) = d

-- ******************

-- Projecções sobre relaçoes
pr1 (a,_,_) = a
pr2 (_,b,_) = b
pr3 (_,_,c) = c
-- *********





vaz :: LTS
vaz = ([],[],[],[])

vaz2 :: LTS
vaz2 = ([],[],[],[])

-- ****************

-- Def Operadores 
(<=>) :: Bool -> Bool -> Bool -- Equivalencia Definida..
a <=> b  =  (a<=b) && (b<=a)

singl x = [x]

(+++) :: (Eq a) => a -> [a] -> [a]
(+++) a x = if (elem a x) then x
							else (++) x [a]

-- primeira lista exepto a segunda l / l2
(<<) :: (Eq a) => [a] -> [a] -> [a]
(<<) l [] = l
(<<) [] l = []
(<<) l (h:t) = (<<) (removeH h l) t


-- **********

-- Conjunto transições tem que ser igual, não tem mas convém.. "over N"

removeH :: (Eq  a) => 	a -> [a] -> [a]
removeH x [] = []
removeH x (h:t) | x == h = t
                | otherwise = h:(removeH x t)

checkN :: (Eq a) => ([a],[a]) -> Bool
checkN ([],[]) = True
checkN ([], l) = False
checkN (l ,[]) = False
checkN ((h:t),l) | elem h l = checkN (t, removeH h l)
				 | otherwise = False



-- **************************************

-- Dá a relação de um State dado

stateR :: (State, LTS) -> R
stateR (x,y) =  filter ((x==).pr1) (pl4  y)

-- ************************


--IMPORTANTE 1a cond de BS
eFinal :: (State,LTS) -> Bool -- Testa se um State é final ou não
eFinal = (uncurry elem).(id >< pl3)

primeira_condicao :: ((State,LTS),(State,LTS)) -> Bool -- Primeira condição de Bissimulação !!
primeira_condicao = (uncurry (<=>)).(eFinal >< eFinal)
-- *************


func' :: Transition -> (State,LTS) -> R
func' t = filter ((t==).pr2).stateR 

{- 
rXr :: ((State,LTS),(State,LTS)) -> (R,R) -- alteração para permitir a aplicação do operador >< de forma explicita !!!
rXr = stateR >< stateR
-}

relPar :: Transition -> ((State, LTS),(State, LTS)) -> (R,R)
relPar t = ((func' t) >< (func' t))
 

-- para cada par de States, verifica as suas transiçoes com todo o conjunto N

relParList :: N -> ((State, LTS),(State, LTS)) -> [(R,R)]
relParList [] x = []
relParList (h:t) x = (relPar h x):(relParList t x)

conjRelacoes :: ((State,LTS),(State,LTS)) -> [(R,R)]
conjRelacoes ((e,l),(e2,l2)) =  relParList (pl2 l) ((e,l),(e2,l2))


-- dá os pares de State recentemente processados, resultado da analise d par anterior

rXr' l = [ (x,y) | x <- (p1 l), y <- (p2 l)]

recProc :: (R,R) -> [(State, State)]
recProc  = rXr' . ((map pr3) >< (map pr3)) 

		
recProcGeral :: [(R,R)] -> [(State,State)]
recProcGeral  = concat . (map recProc)



recProcFinal = recProcGeral.conjRelacoes
 	       
-- ******************

ver :: (R,R) -> BS (R,R)
ver ([],[]) = Yes ([],[])
ver (l, []) = No (l,[])
ver ([], l)= No ([],l)
ver (l,l2)  = Yes (l,l2)






logic :: BS a -> Bool
logic (Yes _) = True
logic (No _ ) = False


lookUpB :: [BS a] -> Bool
lookUpB [] = True
lookUpB (h:t) = if (logic h) then lookUpB t
						else (logic h)

viaveis = (uncurry (&&)) . (split (lookUpB.(map ver).conjRelacoes) (primeira_condicao))





type Ep = [(State,State)]
type Actual = (State,State)
type Erp = [(State,State)]
type Ec = [(State,State)]

type Tudo = (Ep,Actual,Erp,Ec) 

iso' ::  (Tudo,(LTS,LTS)) -> ((State, LTS), (State, LTS))
iso' =  (split ((p1.pl2) >< p1) ((p2.pl2) >< p2))

coloca_erp :: (Tudo, Erp) -> Tudo
coloca_erp ((x,y,z,w),l) = (x,y,z++l,w)

actualToEp :: Tudo -> Tudo
actualToEp (x,y,w,z) = (x++singl(y),y,w,z) 

existem_todos :: (Eq a) => [a] -> [a] -> Bool
existem_todos [] l = True
existem_todos (h:t) x = (elem h x) && (existem_todos t x)

teste4 :: Tudo -> Bool
teste4 x = (existem_todos (pl3 x) ( (pl4 x) ++ (pl1 x)) ) && ((pl4 x) == [])


actualizaErpToEc :: Tudo -> Tudo
actualizaErpToEc (x,y,z,w) = (x,y,[],erpToEc(z,x,w)++w)

calculadosToActual :: Tudo -> Tudo
calculadosToActual (x,y,z,w) = (x,head w,z, tail w)

erpToEc :: (Ep,Erp,Ec) -> Ec
erpToEc (e, er, c) =  e << (er++c)

{--
maquina :: Int -> (Tudo,(LTS,LTS)) -> (Int ,BS Tudo)
maquina 0 =   cond (viaveis . iso')  (maquina 1) (split (const 0)  (No . p1))
maquina 1 = (maquina 2) . (split (actualToEp . coloca_erp . (split p1 (recProcFinal . iso'))) p2)
maquina 2 = cond (teste4 . p1) (split (const 2) (Yes . p1)) ((maquina 0) . (split (calculadosToActual . actualizaErpToEc . p1) p2) )
--}

maquina :: (Tudo,(LTS,LTS)) -> BS Tudo
maquina = cond (viaveis . iso')  ((cond (teste4 . p1)  (Yes . p1) ((maquina) . (split (calculadosToActual . actualizaErpToEc . p1) p2))) . (split (actualToEp . coloca_erp . (split p1 (recProcFinal . iso'))) p2)) (No . p1)


converTe :: ((State,LTS),(State,LTS)) -> (Tudo,(LTS,LTS))
converTe ((x,lt),(x',lt')) = (([],(x,x'),[],[]),(lt,lt')) 

--algBiss :: ((State,LTS),(State,LTS)) -> (Int,BS Tudo)
--algBiss = (maquina 0). converTe

algBiss :: ((State,LTS),(State,LTS)) -> BS Tudo
algBiss = maquina . converTe








