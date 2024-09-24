{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Lib where

import Data.Set (Set)

-- | Credits to TODO
-- Just guessing the types or stubbing them

-- | MDP States
data S = S Int

-- | MDP Booleans
data A = A Bool

-- | Probablistic Transition Function
type P = (S, A) -> Set (S, Float)

-- | Reward funtion
type R = (S, A, S) -> Float

-- | Markov Decision Process
data MDP = MDP {
  _S :: Set S
  , sᵢ :: S -- Initial state
  , _A :: Set A -- Finite set of boolean actions
  , _P :: P
  , _R :: R
}

-- Automata States
data Q = Q Int

-- Transition
type Transition _Σᵢ = (Q, _Σᵢ) → _Σᵢ

-- A finite state reactive system
data S q _Σᵢ _Σ₀ = S {
  _Q :: Set Q
  , q₀ :: Q
  , _Σᵢ :: _Σᵢ
  , _Σ₀ :: _Σ₀
  , δ :: Transition q _Σᵢ
  }

-- Safety automation φˢ
data SafetyAutomation _Σ = SafetyAutomation {
  q :: Set Q
  , q₀:: Q
  , sigma :: _Σ
  , δ :: Transition Q _Σ
  , _F :: Set Q -- Set of safe states
  }
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
        _Σᵢ = undefined
        _Σₒ= undefined
        δ' = undefined -- (g, σᵢ ) = (g, σᵢ, ρ(g, σᵢ))
        ρ = undefined
    in S q _Σᵢ _Σₒ δ'
