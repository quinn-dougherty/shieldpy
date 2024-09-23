{-# LANGUAGE UnicodeSyntax #-}

module Lib where

import Data.Set (Set)

-- | Credits to TODO
-- I try my best to match unicode to the paper I find that's easier to map even if it might be annoying to setup.
-- Some unicode characters are prepended with _ for variable names.
-- If you use emacs you can use latex input mode to type unicode characters.

-- States
-- TODO
data Q = Q Int

-- Game States
-- data S = S Int

-- Transition
type Transition q _Σᵢ = (q, _Σᵢ) → _Σᵢ

-- Safety automation φˢ
data SafetyAutomation _Σ = SafetyAutomation {
  q :: Set Q
  , q₀:: Q
  , sigma :: _Σ
  , δ :: Transition q _Σ
  , _F :: Set Q -- Set of safe states
  }

-- A finite state reactive system
data S q sigma_i sigma_o = S (Set q)  q sigma_i sigma_o (Delta sigma_i)

-- | Used for synthesizing the shield
-- Defines a set Fᵍ  ⊆ G of safe states
-- Where win(g₀, g₁, ...) iff ∀i ≥ 0. gᵢ ∈ Fᵍ
-- I think we can solve for this using SMT. In the original implementation they used BDDs.
safetyGame ∷ G -> G
safetyGame g = undefined

  -- | Uses the safety game to synthesize a shield which implements the winning strategy in a new reactive system (Is it a finite reactive system?)
shield ∷ S
shield =
    let g = undefined
        q = undefined
        sigma_I = undefined
        sigma_O = undefined
        δ' = undefined -- (g, σᵢ ) = (g, σᵢ, ρ(g, σᵢ))
        ρ = undefined
    in undefined
