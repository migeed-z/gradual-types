{-# Language DeriveFoldable #-}
{-# Language DeriveFunctor #-}
{-# Language DeriveDataTypeable #-}
{-# Language MultiParamTypeClasses #-}
{-# Language DeriveTraversable #-}
{-# Language LambdaCase #-}
{-# Language FlexibleContexts #-}
{-# Language TypeOperators #-}
{-# Language TemplateHaskell #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleContexts #-}
{-# Language ViewPatterns #-}


--capture avoidance not accounted for in this solver
module Analysis where
import Data.Data
import Data.List as List
import Data.Comp.Variables
import Data.Comp.Unification
import Data.Comp.Term
import Data.Comp.Derive
import Constraints
import Data.Bool(bool)
import Control.Monad(liftM2)
import Syntax
import Constraints
import Data.Maybe (fromJust)
import Data.Maybe (isJust)
import qualified Data.Map as Map
import Syntax
import Data.List as List
import Control.Monad
import Checker
import Syntax
import Constraints
import Encoding
import Logic


--Data structures 
isCType :: CType -> Bool
isCType CInt = True
isCType CDyn = True
isCType CBool = True
isCType (CArr t1 t2) = (isCType t1) && (isCType t2)
isCType _ = False

--extract numbers from type variables
extract_num :: CType -> Int
extract_num (CVar n) = n

data CTypeF a 
    = CVarF Int 
    | CArrF a a
    | CIntF
    | CDynF
    | CBoolF
    deriving (Data, Functor, Foldable, Traversable, Show, Eq)

$(makeShowF ''CTypeF)

instance HasVars CTypeF Int where
    isVar (CVarF x) = Just x
    isVar (CArrF x y) = Nothing
    isVar CIntF = Nothing
    isVar CBoolF = Nothing
    isVar CDynF = Nothing

type CType_ = Term CTypeF

ctypeTof :: CType -> CType_
ctypeTof CInt = Term CIntF
ctypeTof CBool = Term CBoolF
ctypeTof CDyn = Term CDynF
ctypeTof (CVar i) = Term (CVarF i)
ctypeTof (CArr a b) = Term (CArrF (ctypeTof a) (ctypeTof b))


toFequations :: [Constraint] -> (Equations CTypeF)
toFequations [] = []
toFequations ((Equality a b) : xs) = ((ctypeTof a), (ctypeTof b)) : (toFequations xs)
toFequations (x : xs) = (toFequations xs) 

unravel :: CType_ -> CType
unravel a = 
    case unTerm a of 
        CVarF i -> CVar i
        CArrF a b -> CArr (unravel a) (unravel b)
        CIntF -> CInt
        CBoolF -> CBool
        CDynF -> CDyn 

------------------------------------------------------------------

--First, we need functions that construct simPrec, simCon, a constraint solver 
-- using these components.

--simPrec

--simprec for a single constraint
simPrec_sing :: (CType, Constraint) -> (CType, [Constraint])
simPrec_sing (ctyp, cons) = snd $ runState (go (ctyp, cons)) (extract_num ctyp + 1) where
  go ::  (CType, Constraint) -> State Int (CType, [Constraint])

  go (ctyp, cons) = do 
   case cons of
      (Precision CDyn (CVar n)) -> do
        return (ctyp, [])  

      (Precision CBool (CVar n)) -> do
        return (ctyp, [(CVar n) .= CBool])
     
      (Precision CInt (CVar n)) -> do 
        return (ctyp, [(CVar n) .= CInt])

      (Precision (CArr t1 t2) (CVar v))  -> do 
        v1 <- gen
        v2 <- gen
        return (v2, [(CVar v) .= (v1 .~> v2), (t1 .<= v1), (t2 .<= v2)])

      c -> do
        return (ctyp, [c])



simPrec :: (CType, [Constraint]) ->  (CType, [Constraint])
simPrec (typ, []) = (typ, [])
simPrec (typ, x:xs) = ((fst rstc),(snd fstc) ++ (snd rstc))
    where fstc = (simPrec_sing (typ, x))
          rstc = (simPrec ((fst fstc), xs))

--------------------------------------------------------------------

--simMatch


--Generate all matching possibilities for one constraint
match :: Constraint -> [(Int, [Constraint])]
match (Matching (CVar v)(CArr (CVar v1)(CVar v2))) = 
  [ (1, [ (CVar v) .=  ((CVar v1) .~> (CVar v2)) ])
  , (2, [ (CVar v) .= CDyn
        , (CVar v1) .= CDyn
        , (CVar v2) .= CDyn
        ]
    )
  ] 
match x = 
  [(0, [x])]


--generate all matching possibilities for a set of constraints
simMatch :: [Constraint] -> [[Constraint]]
simMatch cs = map concat . sequence $ 
  [ map snd (match c)
  | c <- cs
  ]

--generate all matching possibilities for a set of constraints
-- this version also numbers the constraints
simMatch' :: [Constraint] -> [([Int], [Constraint])]
simMatch' cs = map fn . sequence $ 
  [ match c
  | c <- cs
  ]
  where
    fn :: [(Int, [Constraint])] -> ([Int], [Constraint])
    fn ls = (map fst ls, concatMap snd ls)

--------------------------------------------------------------------

--simCon

--simCon for a single constraint
simConSing:: Constraint -> Maybe [Constraint]
simConSing (Consistency (CArr t1 t2) CBool) = Nothing
simConSing (Consistency (CArr t1 t2) CInt) = Nothing
simConSing (Consistency CBool (CArr t1 t2)) = Nothing
simConSing (Consistency CInt (CArr t1 t2)) = Nothing
simConSing (Consistency CBool CInt) = Nothing
simConSing (Consistency CInt CBool) = Nothing
simConSing (Consistency CBool CBool) = Just []
simConSing (Consistency CInt CInt) = Just []
simConSing (Consistency t CDyn) = Just []
simConSing (Consistency CDyn t) = Just []
simConSing (Consistency (CArr t1 t2) (CArr t1' t2')) = 
                        Just [(Consistency t1 t1'),
                              (Consistency t2 t2')]
simConSing (Consistency (CVar v1) (CVar v2)) = Just [(Consistency (CVar v1) (CVar v2))]
simConSing (Consistency t (CVar v)) = Just [(Consistency (CVar v) t)]

simConSing c = Just [c]


--simCon for a set of constraints
simCon :: [Constraint] -> Maybe [Constraint]
simCon [] = Just []
simCon (x:xs) = case ((simConSing x), (simCon xs))  of
              (Nothing, _) -> Nothing
              (_, Nothing) -> Nothing
              (Just lst, _) -> Just (lst ++ (concat (simCon xs)))



  --------------------------------------------------------------------

-- Unification

--calls the unification algorithm on the equality
call_unifier :: [Constraint] -> Either (UnifError CTypeF Int) (Subst CTypeF Int)
call_unifier c = (unify (toFequations c))

pleaseUnify :: [Constraint] -> Either String [(Int, CType)]
pleaseUnify cnt = case (call_unifier cnt) of
  Left (FailedOccursCheck v term) -> 
    Left ("failed occurs check " ++ show v ++ ": " ++ (show $ unravel term))
  Left (HeadSymbolMismatch t1 t2) -> 
    Left ("head symbol mismatch " ++ show (unravel t1)  ++ " =/= " ++ (show $ unravel t2))
  Left (UnifError str) -> 
    Left str
  Right (subst :: Subst CTypeF Int) -> 
    Right (Map.toList $ fmap unravel subst)


--apply unifier to consistency constraints
getConsistConst :: [Constraint] -> [Constraint]
getConsistConst [] = []
getConsistConst (Consistency c1 c2 :xs) = 
    (Consistency c1 c2) : (getConsistConst xs)
getConsistConst (x:xs) = (getConsistConst xs)


--substitute type in solution
substituteSol :: CType -> [(Int, CType)] -> CType

substituteSol (CVar x) (List.lookup x -> Just t) = t
substituteSol (CArr v1 v2) sol = (CArr (substituteSol v1 sol)  
                                       (substituteSol v2 sol))
substituteSol t sol = t

-- Given a set of constraints and a substitution, apply the substituition
-- to the set of contraints. 
apply_unifier ::  [Constraint] -> [(Int, CType)] -> [Constraint]
apply_unifier  [] sol = []
apply_unifier ((Consistency v1 v2):xs) sol = (Consistency (substituteSol v1 sol) 
                                                    (substituteSol v2 sol)) :
                                        (apply_unifier xs sol)
apply_unifier (x:xs) sol = (apply_unifier xs sol)

--------------------------------------------------------------------



--some parts of this code do not follow the exact structure given
-- by the psudocode. Particularly, in the parts that use
-- \exists (v~t), we must have a constructive solution
-- which leads to some implementation details outlined below


check_var_limits :: [[Constraint]] -> Bool
check_var_limits cnst = not (elem False 
                       [(boundnessOneSet cnst_set cnst_set) | 
                        cnst_set <- cnst]) 

--auxilary functions:

--ensures that the type does not have any occurrence of dyn
hasStaticLeaf :: CType -> Bool
hasStaticLeaf CInt = True
hasStaticLeaf CBool = True
hasStaticLeaf (CArr t1 t2) = (hasStaticLeaf t1) && 
                             (hasStaticLeaf t2)
hasStaticLeaf _ = False


-- 0 = left
-- 1 = right
-- 2 = left and right

boundnessOneVar :: CType -> [Constraint] -> Int -> Bool
boundnessOneVar (CVar v) [] direc = True
boundnessOneVar (CVar v1) ((Consistency (CVar v2) CInt) :xs) direc | v1 == v2 = True 
boundnessOneVar (CVar v1) ((Consistency (CVar v2) CBool):xs) direc | v1 == v2 = True

boundnessOneVar (CVar v1) ((Consistency (CVar v2) (CArr t1 t2)):xs) 2 | v1 == v2 = 
  case ((hasStaticLeaf t1),(hasStaticLeaf t2)) of 
    (True, True) -> True
    (True, False) -> (boundnessOneVar (CVar v1)  xs 1)
    (False, True) -> (boundnessOneVar (CVar v1)  xs 0)
    (False, False) -> (boundnessOneVar (CVar v1)  xs 2)


boundnessOneVar (CVar v1) ((Consistency (CVar v2) (CArr t1 t2)):xs) 1 | v1 == v2 = 
  case ((hasStaticLeaf t1),(hasStaticLeaf t2)) of 
    (_, True) -> True
    otherwise -> (boundnessOneVar (CVar v1)  xs 1)

boundnessOneVar (CVar v1) ((Consistency (CVar v2) (CArr t1 t2)):xs) 0 | v1 == v2 = 
  case ((hasStaticLeaf t1),(hasStaticLeaf t2)) of 
    (True, _) -> True
    otherwise -> (boundnessOneVar (CVar v1)  xs 0)

boundnessOneVar (CVar v) (x:xs) direc = (boundnessOneVar (CVar v) xs direc) 


boundnessOneSet :: [Constraint] -> [Constraint] -> Bool
boundnessOneSet [] _ = True 
boundnessOneSet ((Consistency (CVar v) c) : xs) lst = (boundnessOneVar (CVar v) lst 2) &&
                                                      (boundnessOneSet xs lst)

-----------------------------------------------------------------

-- Compose all operations upto the simMatch
compose_upto_match :: Expr -> Env -> [[Constraint]]
compose_upto_match expr env = (simMatch (snd (fixed simPrec (constraint expr env))))


--compose all steps upto simCon
solve_constraints :: Expr -> Env -> [Maybe [Constraint]]
solve_constraints expr env = [fixedM simCon c | c <- (map snd (apply_unifier_to_2n (compose_upto_match expr env)))]


-- Solve the family of constraint sets and remove the sets which have no solution
-- for a given set of constraints, we return the list of variables
-- that were in the domain of the unification solution. Then we return 
-- the constraints resulting from the substitution 
apply_unifier_to_2n :: [[Constraint]] -> [([Int],[Constraint])]
apply_unifier_to_2n [] = []
apply_unifier_to_2n (x:xs) = case (pleaseUnify x) of 
          (Left _) -> (apply_unifier_to_2n xs)
          (Right sol) -> ((map fst sol),(apply_unifier x sol)) : (apply_unifier_to_2n xs)


check_termination :: Expr -> Env -> Bool
check_termination e env = (check_var_limits (extract_valid c)) &&
                        (verify_counts (collect_all_vars (snd (constraint e env))) 
                        [collect_all_vars_rhs s | s <- (extract_valid c)]
                        (get_empty_domains (substitution_domains e env) c))
                where c = (solve_constraints e env)


-----------------------------------------------------------------

--auxilary functions
--note that when we collect variables, we ensure there are no duplicates
-- so it is enough to check the length (using rmdups function)
verify_counts :: [Int] -> [[Int]] -> [[Int]] -> Bool
verify_counts l1 [] [] = True
verify_counts l1 (x1:xs1) (x2:xs2) = (length l1) == ((length x1) + (length x2)) && (verify_counts l1 xs1 xs2)
                                 

-- for every contraint set, these will be the list of variables used in the domain of the solution 
substitution_domains :: Expr -> Env -> [[Int]]
substitution_domains e env =  (map fst (apply_unifier_to_2n (compose_upto_match e env)))


-- collect all type variables in a set of constraints 
collect_all_vars :: [Constraint] -> [Int]
collect_all_vars [] = []
collect_all_vars (x:xs) = rmdups( (collect_free_vars_cnst x) ++ (collect_all_vars xs))


-- collect all type variables appearing on the right hand side of a set of constraints 
collect_all_vars_rhs :: [Constraint] -> [Int]
collect_all_vars_rhs [] = []
collect_all_vars_rhs (x:xs) = rmdups( (collect_free_vars_cnst_rhs x) ++ (collect_all_vars_rhs xs))

-- collect all type variables appearing in a constraint
collect_free_vars_cnst :: Constraint -> [Int]
collect_free_vars_cnst (Matching v1 v2) = (collect_free_vars v1) ++ (collect_free_vars v2)
collect_free_vars_cnst (Consistency v1 v2) = (collect_free_vars v1) ++ (collect_free_vars v2)
collect_free_vars_cnst (Equality v1 v2) = (collect_free_vars v1) ++ (collect_free_vars v2)
collect_free_vars_cnst (Precision v1 v2) = (collect_free_vars v1) ++ (collect_free_vars v2)


-- collect all type variables appearing on the right handside of a constraint
collect_free_vars_cnst_rhs :: Constraint -> [Int]
collect_free_vars_cnst_rhs (Matching v1 v2) = (collect_free_vars v1) 
collect_free_vars_cnst_rhs (Consistency v1 v2) = (collect_free_vars v1) 
collect_free_vars_cnst_rhs (Equality v1 v2) = (collect_free_vars v1) 
collect_free_vars_cnst_rhs (Precision v1 v2) = (collect_free_vars v1) 


-- collect all type variables from one type. 
collect_free_vars :: CType -> [Int]
collect_free_vars (CVar v) = [v]
collect_free_vars (CArr v1 v2) = (collect_free_vars v1) ++ (collect_free_vars v2)
collect_free_vars _ = [] 


-- a 'Nothing' in the set of constraints signify that there was no solution
-- so we must remove its corresponding (empty) list of variables from the set
get_empty_domains :: [[Int]] -> [Maybe [Constraint]] -> [[Int]]
get_empty_domains [] [] = []
get_empty_domains (x:xs) (Nothing : xs2) = (get_empty_domains xs xs2)
get_empty_domains (x:xs) (x1 : xs2) = (x: (get_empty_domains xs xs2))
get_empty_domains ints _ = ints


extract_valid :: [Maybe [Constraint]] -> [[Constraint]]
extract_valid lst = [(fromJust x) | x <- lst, (isJust x)]

--run functions till fixed point
fixed_uni :: Eq a => (a -> b -> a) -> a -> b -> a
fixed_uni f a b
  | a == a' = a
  | otherwise = fixed_uni f a' b
  where a' = f a b


-- call function till fixed point (different variations)
fixed :: Eq a => (a -> a) -> a -> a
fixed f a 
  | a == a' = a
  | otherwise = fixed f a'
  where a' = f a


fixedM :: (Eq a, Monad m) => (a -> m a) -> a -> m a
fixedM f = go
    where go x = f x >>= liftM2 bool go pure <*> (x ==)

--removes all duplicates from a given list
rmdups :: (Ord a) => [a] -> [a]
rmdups = map head . group . sort
