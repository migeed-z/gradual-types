{-# Language QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Hspec
import Samples
import Data.List
import Migration
import Checker
import Syntax
import Constraints
import Analysis
import Data.Either
import Data.Maybe
import qualified Data.Map as Map

main :: IO ()
main = test

test :: IO ()
test = hspec $ do
    test_topchoice
    test_finitness

test_topchoice :: Spec
test_topchoice = describe "Top choice check" $ do

    example (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) True
    example succ_lam_true  True
    example my_lam True
    example simple_app True

    where
        example :: Expr -> Bool -> Spec
        example term expected = do
            it ("sees that " ++ show term ++ " has a top choice? =  " ++ show expected) $ do
                (length(find_top term tenv) == 1) `shouldBe` expected

test_finitness :: Spec
test_finitness  = describe "Finitness check" $ do

    example (Lam Tdyn "x" (App (Vv "x") (App (Vv "succ") (Vv "x")))) True
    example succ_lam_true True
    example my_lam True
    example simple_app True
    example (App (Vv "succ") (App(Lam Tdyn "y" (Vv "y"))
                (App (Lam Tdyn "x" (Vv "x"))(Vb True)))) True
    example (Lam Tdyn "x" (Vv "x")) False
    example lam_xyy False
    example evil False
    example evil_example False
    example self_application False
    example lam_term_1 False
    example app_term_2 False
    example (Lam Tdyn "x" (App (Vv "succ") (App (Vv "x") (Vv "x")))) False

    where
        example :: Expr -> Bool -> Spec
        example expr expected = do
            it ("sees that " ++ show expr ++ " is finite? = "
                                       ++ show expected) $ do
                check_termination expr tenv `shouldBe` expected
