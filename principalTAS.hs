-- In the following an Haskell encoding of the main concepts defined in the article ...
-- The encoding is quite direct and gives a normalization algorithm for the lambda calcus

-- data defining the syntax for names, the constructor "Ln", "Rn" are used
-- to allow the creation of two new versions of any given name,
data Name  = Bn Char |  Ln Name  | Rn Name 
  deriving Eq
instance Show Name where
  show (Bn x) =  [x]
  show (Ln n) = show n  ++  "l"
  show (Rn n) = show n  ++  "r"

-- data defining the syntax for type
-- Ar stand for the arrow type constructor
-- And is the intersection type constructor
data Type = Var Name | Ar Type Type | Bang Type | Box Name Type | And Type Type  | Empty
  deriving Eq
instance Show Type where
  show (Var a) = show a
  show (Ar sigma tau) = "(" ++ show sigma ++ " -> " ++  show tau ++ ")"
  show (Bang tau)   = "!"++ show tau
  show (Box i tau)   = "□" ++ show i ++ " "++ show tau
  show (And tau1 tau2) = "(" ++ show tau1 ++ " /\\ " ++  show tau2 ++ ")"
  show (Empty) = "0"

-- to simplify the recursive definition of variuous functions
-- on types, it is convenient to introduce the following operator
recType
  ::    (Name -> t)
     -> (t -> t -> t)
     -> (t -> t)
     -> (Name -> t -> t)
     -> (t -> t -> t)
     -> t
     -> Type
     -> t
recType va ar ba bo an em tau =
  case tau of
    Var a  -> va a 
    Ar si ta -> ar (recType va ar ba bo an em  si) (recType  va ar ba bo an em  ta)
    Bang ta  -> ba  (recType va ar ba bo an em  ta)
    Box i ta -> bo i (recType va ar ba bo an em  ta)
    And ta1 ta2 -> an (recType va ar ba bo an em  ta1) (recType va ar ba bo an em  ta2)
    Empty -> em

-- in the following the definition of the basic operators of substitution, duplication and
-- cancellation on types 

-- (substitute n sigma1 sigma2) returns the type sigma2 modified
-- by replaceing each variable (Var n) by sigma1
substitute :: Name -> Type -> Type -> Type
substitute a  tau  = recType (subVar a  tau ) Ar Bang Box And Empty
subVar :: Name -> Type -> Name -> Type
subVar a  tau  a1 = if a == a1 then  tau  else Var a1

-- (duplicate i sigma)
-- duplicates all subterms sigma having (Box i) as main connective
duplicate :: Name -> Type -> Type
duplicate i  = recType Var Ar Bang (dupBox i) And Empty
--dupBox n = Box
dupBox i j tau = if i == j then  And (rename True (Box j tau)) (rename False (Box j tau)) else Box j tau

-- duplicate uses the following auxiliary function

-- (remame b sigma) return the type sigma modified
-- by replaceing each name appearing in sigma by its left or right version, depending on b
rename :: Bool -> Type -> Type
rename b = recType (Var . (renameN b)) Ar Bang (Box . (renameN b)) And Empty
renameN b n = if b then Ln n else Rn n

-- similarly to duplicate, (delete i sigma)
-- delete all subterms sigma having (Box i) as main connective
delete :: Name -> Type -> Type
delete i  = recType Var Ar Bang (delBox i) delAnd Empty
delBox i j tau = if  (i == j)  then Empty else Box j tau
--  delBox i j tau = if  (i == j) || (tau == Empty) then Empty else Box j tau  -- version that clear some useless boxes
delAnd tau1 tau2 = if (tau1 == Empty) then tau2 else if (tau2 == Empty) then tau1 else And tau1 tau2

-- (replace i l sigma) returns the type sigma modified
-- by expanding each Box with index i with a list of boxes having as indexes the names in l
replace :: Name -> [Name] -> Type -> Type
replace n l = recType Var Ar Bang (replaceBox n l) And Empty
replaceBox i l j tau | i == j = makeListBoxes l tau
                     | True   = Box j tau
  where makeListBoxes []         tau = tau
        makeListBoxes (i1 : ls)  tau  = Box i1 (makeListBoxes ls tau)


-- the following is a direct translation of the
-- MGU rules presented in the article
mgu :: Type -> Type -> Type -> Type
mgu sigma (Var a) = substitute a sigma
mgu (Var a)  tau  = substitute a tau
mgu (Ar tau1 sigma2)(Ar sigma1 tau2) =  
  let u1 = mgu sigma1 tau1 in 
      mgu (u1 sigma2) (u1 tau2) . u1 
mgu (Box j sigma)(Box i tau) =  (mgu sigma (Box i tau)) . (replace i [j,i]) 
mgu (Bang sigma) (Box i (Bang tau)) = (mgu  sigma tau) . (replace i [])
mgu (And sigma1 sigma2)(Box i tau) =  
  let u1 = mgu sigma1 (rename True (Box i tau)) in 
      mgu (u1 sigma2) (u1 (rename False (Box i tau))) . u1 . (duplicate i)
-- mgu Empty (Box i sigma) = delete i
mgu Empty (Box i sigma) = replace i []
mgu sigma tau = error ("impossible to unify " ++ show sigma ++ " with " ++ show tau)


-- the following is an encoding of the lambda terms
-- LV (lambda variable) used to introduce variable as terms,
-- LAb (linear lambda abstraction),
-- App (application), Ba (Bang, "of course" operator)
data LamTerm = LV Name  |  LAb Name LamTerm | App LamTerm LamTerm | Ba LamTerm
  deriving Eq
instance Show LamTerm where
  show (LV x)  = show x 
  show (LAb x p) = "\\" ++  show x ++ "->" ++ show p 
  show (App p q) = "(" ++show p ++ "." ++ show q ++ ")"
  show (Ba p) = "!" ++show p

-- data representing the type assignment for a given lambda term "m"
-- the associate type assignment (TyAs env sigma) define:
-- the type sigma associate to m,
-- the list "env" defining an environment for the free variables of m 
data TypeAssignment =TyAs [(Name, Type)]  Type
instance Show TypeAssignment where
  show (TyAs env tau) =  show env ++ " |- " ++ show tau

-- the following are some auxiliary functions acting on environments 
-- (envExtract x l) search in the variable x is defined in the environment l
-- in case return the associated type and the environment purge from the variable x
envExtract :: Name -> [(Name, Type)] -> Maybe (Type, [(Name, Type)])
envExtract x l = envExtractAux x l [] where
  envExtractAux x [] lc = Nothing
  envExtractAux x ((y, tau):l) lc = if (x == y) then Just(tau, lc ++ l)
                                    else envExtractAux x l ((y,tau):lc)

-- function that build the meet of two environments
envAnd :: [(Name, Type)] -> [(Name, Type)] -> [(Name, Type)]
envAnd [] env = env
envAnd ((x,tau): env1) env2 = case envExtract x env2 of
                               Nothing -> (x,tau): envAnd env1 env2
                               Just (tau1,env3) -> (x, (And tau tau1)): envAnd env1 env3

-- a functional that apply the function to each type component in a environment
applyTypes f = map (\ (x,y) -> (x, f y))

-- streams of new names
charsFrom a = a : charsFrom (toEnum (fromEnum a + 1))
streamNewVarType = map Bn (charsFrom 'α')
streamNewIndex   = map Bn (charsFrom 'a')

-- the following is a almost straightforward translation of type assignment rules that
-- given a lambda terms "m" finds a type assignment for it
-- as extra parameters the function takes:
-- a stream of new names type variable "nt"
-- a stream of new name for index "ni"
-- the function beside returning the type assignment returns also an update
-- of the streams of new names, that is, if a new names is used is removed from the stream
deriveType :: [Name] -> [Name] -> LamTerm -> ([Name], [Name], TypeAssignment)
deriveType (alpha:nt) ni (LV x) = (nt, ni, (TyAs [(x, Bang (Var alpha))] (Var alpha)))

deriveType  nt (i:ni)  (Ba m) = let (ntr, nir, (TyAs  env tau)) = deriveType nt ni m
                                  in  (ntr, nir, (TyAs  (applyTypes (Box i) env) (Box i (Bang tau))))

deriveType  nt ni (App m n) = case deriveType nt ni m of
                                   (nt1, ni1, (TyAs env1 (Var alpha))) ->
                                     case deriveType nt1 ni1 n of
                                       (nt2, ni2, (TyAs env2 sigma)) ->
                                         let unS = applyTypes (substitute alpha (Ar sigma (Var alpha)))
-- version using a new name beta, as in the article, but not necessary
--                                     ((beta:nt2), ni2, (TyAs env2 sigma)) ->  
--                                        let unS = applyTypes (substitute alpha (Ar sigma (Var beta)))
                                             env3 = unS (envAnd env1 env2)                                
                                         in (nt2, ni2, (TyAs env3 (Var alpha)))
--                                       in (nt2, ni2, (TyAs env3 (Var beta)
                                   (nt1, ni1, (TyAs env1 (Ar tau sigma1))) ->
                                     case deriveType nt1 ni1 n of
                                       ((beta:nt2), ni2, (TyAs env2 sigma)) ->
                                         let un = mgu tau sigma
                                             unS = applyTypes un
                                             env3 = unS (envAnd env1 env2)                                
                                         in (nt2, ni2, (TyAs env3 (un sigma1)))

deriveType nt ni (LAb x p) = let (ntr, nir, (TyAs env tau)) = deriveType nt ni p
                                in case (envExtract x env) of 
                                    Just (sigma, envt) -> (ntr, nir, (TyAs envt (Ar sigma tau)))
                                    Nothing ->  (ntr, nir, (TyAs env (Ar Empty tau)))

-- two simplified functions that given a (closed) term, returns its (type) type assignment  

derType m = let (_, _, (TyAs _ tau)) = deriveType streamNewVarType streamNewIndex m
            in tau               
derTypeOpen m = let (_, _, (TyAs env tau)) = deriveType streamNewVarType streamNewIndex m
                in (TyAs env tau)


-- -- some auxiliary function used in the checking 
-- derPairTypes m1 m2 = let (nt1, ni1, (TyAs _ _ tau1)) = deriveType streamNewVarType streamNewIndex [] m1
--                          (_, _, (TyAs _ _ tau2))     = deriveType nt1 ni1 [] m2
--                      in (tau1, tau2)     

-- derUnifTypes m1 m2 = let (Ar sigma tau, tau2) = derPairTypes m1 (Ba m2)
--                          u = mgu sigma tau2
--                      in (u(Ar sigma tau), u tau2)




-- next we aim to define a functions that given a principal type
-- constructs the corresponding lambda term 
-- some auxiliary functions are needed

-- (searchVarNType a sigma l) checks whether the negative type sigma is
-- in the form (tau1 -> tau2 -> ... -> (Var a)
-- in that case it returns the list of types [tau1, tau2, ... ] ++ l
-- otherwise it return Nothing
searchVarNType a (Var b) l | (a == b) = Just l
                           | True     = Nothing
searchVarNType a (Ar  tau sigma) l = searchVarNType a sigma (tau : l)

-- (serchVarAType a sigma) repeats the previous search on all the
-- negative type components of an and-type
searchVarAType a (Bang sigma) = searchVarNType a sigma []
searchVarAType a (Box i sigma) = searchVarAType a sigma
searchVarAType a (And sigma1 sigma2) = case searchVarAType a sigma1 of
                                         Nothing -> searchVarAType a sigma2
                                         Just l  -> Just l
searchVarAType a Empty = Nothing                                     
searchVarAType a sigma = error (show sigma ++ "is not an and type ") -- just a check useful in debugging 

-- repeats the previous on a environment
searchVarEnv a [] = Nothing
searchVarEnv a ((x,sigma):es) = case searchVarAType a sigma of
                                      Nothing -> searchVarEnv a es
                                      Just l  -> Just (x, l)

-- here we define the reverse algorithm, it is not completely straightforward                                      

-- (deriveTerm  nt (TyAs env tau)) builds a term, in normal form, having type tau,
-- under the hypothesis that it uses free variables
-- whose types are define in env
-- the parameter nt provide a list of new names for lambda variable
deriveTerm  nt (TyAs env (Bang tau)) = Ba (deriveTerm  nt (TyAs env tau))
deriveTerm  nt (TyAs env (Box i tau)) = deriveTerm  nt (TyAs env tau)
deriveTerm  nt (TyAs env (Ar (Box i sigma) tau))  =
  deriveTerm  nt (TyAs env (Ar sigma tau))
deriveTerm  (x : nt) (TyAs env (Ar sigma tau)) =
  LAb x  (deriveTerm  nt (TyAs ((x,sigma):env) tau))
deriveTerm  nt (TyAs env (Var a)) =
  case searchVarEnv a env of
    Just (x, lt) -> buildTerm nt env x lt
    Nothing -> error "strange"  -- just a check useful in debugging -- to be chanced in the alternative TAS

-- auxiliary function for deriveTerm
buildTerm nt env x [] = LV x
buildTerm nt env x (sigma:lt) = App (buildTerm nt env x lt) (deriveTerm  nt (TyAs env sigma)) 

-- a simplified version for 'closed' types 
derTerm sigma = deriveTerm streamNewIndex (TyAs [] sigma)

-- moving from term to type and vice-versa provides a normalisation algorithm 
normalize = derTerm . derType
  
-- here we provide some syntactic sugar for the definition of linear lambda terms 

-- we define a list of usable variables
-- in lambda abstraction one need to use the ' version f'
-- while inside the body one need to use the plain version f
f' = Bn 'f'
g' = Bn 'g'
h' = Bn 'h'
m' = Bn 'm'
n' = Bn 'n'
o' = Bn 'o'
u' = Bn 'u'
x' = Bn 'x'
y' = Bn 'y'
w' = Bn 'w'
z' = Bn 'z'
f = LV f'
g = LV g'
h = LV h'
m = LV m'
n = LV n'
o = LV o'
u = LV u'
x = LV x'
y = LV y'
w = LV w'
z = LV z'

-- application and lambda abstraction defined as infix operators
-- \\ appear between the abstracted variable and the body, like the . in standard notation
-- as usual, application as precedence on lambda abstraction
-- # simulate the application in the standard (non linear) lambda calculus 

(#) m n =  App m (Ba n)
(\\) x m = LAb x m
infixl 9 #
infixr 5 \\


-- the definition of the Church encoding and some basic functions
c0 = f' \\ x' \\ x
cSucc = n' \\ f' \\ x' \\ f # (n # f # x)
cPred = n' \\ f' \\ x' \\ n # (g' \\ h' \\ h #  (g # f)) # ( u' \\ x) #  (u' \\ u)
cPlus = m' \\ n' \\ f' \\ x' \\ m # f  # ( n # f # x)
cMinus = m' \\ n' \\ (n # cPred) # m
cProd = m' \\ n' \\ f' \\ m # (n # f)

-- a function transforming integer in Church numerals 
cEnPreNorm n | (n<=0) = c0
             | True   = cSucc # (cEnPreNorm (n-1))
cEn  = normalize . cEnPreNorm

-- some standard definitions

kay  = x' \\ y' \\ x
false = x' \\ y' \\ y
delta  = x' \\ x # x
omega  = delta # delta
lid  = x' \\ x


-- 2 normal terms whose composition can diverge or converge according to the strategy

en   = z' \\ z # kay # delta
em   = z' \\ z # kay # lid # ( z # false # ( z # false ))
weak = kay # lid # (delta # delta)


-- some casual definitions

c2 =  cEn 2
c22 = c2 # c2
c222 = c22 # c2

c3 = cMinus # cEn 5 # c2
c5 = cPlus # c2 # c3
c6 = cProd # c2 # c3



{--
some notes on an a derivation for M 
let

M =  \ z . z (! K) (! I) (! (z (! F)(!(z (! F)))))

from the hypothesis
z : !(!(!(!(!γ -> γ) -> (0 -> (!γ -> γ))) -> (0 -> (!(!γ -> γ) -> (0 -> (!γ -> γ))))) -> (!(!γ -> γ) -> (0 -> (!γ -> γ))))

one derives:
z : !(!(!(!γ -> γ) -> (0 -> (!γ -> γ))) -> (0 -> (!(!γ -> γ) -> (0 -> (!γ -> γ))))) -> (!(!γ -> γ) -> (0 -> (!γ -> γ)))
!K :  !(!(!(!γ -> γ) -> (0 -> (!γ -> γ))) -> (0 -> (!(!γ -> γ) -> (0 -> (!γ -> γ)))))
K :  !(!(!γ -> γ) -> (0 -> (!γ -> γ))) -> (0 -> (!(!γ -> γ) -> (0 -> (!γ -> γ))))

z(!K) :  (!(!γ -> γ) -> (0 -> (!γ -> γ)))
I : !γ -> γ

z(!K)(!I) : 0 -> (!γ -> γ))
! (z (! F)(!(z (! F)))) : 0

z (! K) (! I) (! (z (! F)(!(z (! F))))) : (!γ -> γ)

by discharging the hypothesis

M : !(!(!(!(!γ -> γ) -> (0 -> (!γ -> γ))) -> (0 -> (!(!γ -> γ) -> (0 -> (!γ -> γ))))) -> (!(!γ -> γ) -> (0 -> (!γ -> γ)))) -> (!γ -> γ)

--}

{-
-- a syntatic definition of the substiutution-replication seen as a list of descriptors of  basic actions

-- The type defines the basic action that can be performed by 
data UnifAction = Sub Name Type | Replace Name [Name] | Duplicate Name | Delete Name | ShowState Type Type
  deriving Eq
instance Show UnifAction where
  show (Sub a tau) = "[" ++ show a ++ " => " ++ show tau ++ "] \n"
  show (Replace i l) = "[" ++ show i ++ "->"  ++ show l ++ "] \n"
  show (Duplicate i) = "Dup(" ++ show i ++ ") \n"
  show (Delete i) = "Del(" ++ show i ++ ") \n"
  show (ShowState sigma tau) = "State(" ++ show sigma ++" = " ++ show tau ++") \n"

unify sigma (Var a) =  (ShowState sigma (Var a) ): [(Sub a sigma)]
unify (Var a)  tau  = (ShowState (Var a)  tau ):  [(Sub a tau)]
unify (Ar tau1 sigma2)(Ar sigma1 tau2) = (ShowState (Ar tau1 sigma2)(Ar sigma1 tau2) ):  
  let u1 = unify sigma1 tau1 in 
      u1 ++ unify (applyUnify u1 sigma2) (applyUnify u1 tau2) 
unify (Box j sigma)(Box i tau) = (ShowState (Box j sigma)(Box i tau) ):   (Replace i [j, i]) : (unify sigma (Box i tau))
-- unify (Box j sigma)(Box i tau) = (ShowState (Box j sigma)(Box i tau) ):   (Replace i [j, Rn i]) : (unify sigma (Box (Rn i) tau))  saver version of the above rule
unify (Bang sigma) (Box i (Bang tau)) = (ShowState (Bang sigma) (Box i (Bang tau))  ):   (Replace i []) : (unify  sigma tau)
unify (And sigma1 sigma2)(Box i tau) = (ShowState (And sigma1 sigma2)(Box i tau) ):  
  let u1 = unify sigma1 (rename True  (Box i tau)) in 
      (Duplicate i) : u1 ++ unify (applyUnify u1 sigma2) (applyUnify u1 (rename False (Box i tau)))
unify Empty (Box i sigma) = (ShowState Empty (Box i sigma) ):   [Delete i]
-- unify sigma tau  = [ShowState sigma tau]

applyAction2Type (Sub a sigma) tau  = substitute a sigma tau
applyAction2Type (Duplicate i ) tau  = duplicate i tau
applyAction2Type (Delete i) tau      = delete i tau
applyAction2Type (Replace i l) tau   = replace i l tau
applyAction2Type (ShowState _ _) tau   =  tau



applyUnify l tau   = foldl (\ pt ac -> applyAction2Type ac pt) tau l
-}
