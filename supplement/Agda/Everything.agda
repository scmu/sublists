{- Agda proofs accompanying the paper 

    Bottom-Up Computation Using Trees of Sublists.
    Shin-Cheng Mu, 2024.

   Tested with Agda version 2.6.4.1 and 
   Agda Standard Library version 2.1.
-}
module Everything where

open import Types
  -- the datatype B and its operations
open import Algorithm
  -- up, subs, ch, td, bu, etc.
open import Naturality
  -- naturality of crucial functions
open import NatProperties
  -- two minor arithmetic properties  
open import Properties
  -- other misc. but important properties 
open import ThmUpgrade
  -- the main theorem about upgrade, that 
  -- it meets the specification
open import ThmBU 
  -- that td = bu