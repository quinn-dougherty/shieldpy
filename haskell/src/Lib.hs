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
data M = M {
  _S :: Set S
  , sᵢ :: S -- Initial state
  , _A :: Set A -- Finite set of boolean actions
  , _P :: P
  , _R :: R
}

-- Automata States
data Q = Q Int deriving (Show, Eq, Ord)

-- Transition
type Transition _Σᵢ = (Q, _Σᵢ) → _Σᵢ

-- | S: A finite state reactive system
-- _Σᵢ: Input alphabet
-- _Σᵢ = _Σᵢ¹ x _Σᵢ²
-- _Σ₀: Output alphabet
data S _Σᵢ¹ _Σᵢ² _Σ₀ = S {
  -- Finite set of states
  _Q :: Set Q
  -- Initial state
  , q₀ :: Q
  -- Input alphabet
  , _Σᵢ :: _Σᵢ
  -- Output alphabet
  , _Σ₀ :: _Σ₀
  -- Transition function
  , δ :: (Q, _Σᵢ) → _Σᵢ
  -- Complete output function
  , λ :: (Q, _Σᵢ) → _Σ₀
  }

type Shield

-- Safety automation φˢ
data SafetyAutomation _Σ = SafetyAutomation {
  q :: Set Q
  , q₀:: Q
  , _Σ :: _Σ
  , δ :: Transition _Σ
  , _F :: Set Q -- Set of safe states
  }
-- | Used for synthesizing the shield
-- Defines a set Fᵍ  ⊆ G of safe states
-- Where win(g₀, g₁, ...) iff ∀i ≥ 0. gᵢ ∈ Fᵍ
-- I think we can solve for this using SMT. In the original implementation they used BDDs.
-- safetyGame ∷ G -> G
-- safetyGame g = undefined

  -- | Uses the safety game to synthesize a shield which implements the winning strategy in a new reactive system (Is it a finite reactive system?)
shield  ∷ Shield _Σᵢ _Σ₀
shield =
    let g = undefined
        q = undefined
        _Σᵢ = undefined
        _Σₒ= undefined
        δ' = undefined -- (g, σᵢ ) = (g, σᵢ, ρ(g, σᵢ))
        ρ = undefined
    in undefined -- TODO S q _Σᵢ _Σₒ δ'

type Σ = Set Int

-- L but maybe just for preemptive shields
-- e.g.  {level < 1, 1 ≤ level ≤ 99, level > 99}
-- type Σᵢ¹ = L

-- A but maybe just for preemtive shields
-- e.g. {Open, Close}
type Σᵢ² = A

-- | Propositions TODO not sure how to represent this
type Prop = String

-- | LTL Formula data type
data LTL
  = AP Prop          -- Atomic proposition
  | Not LTL
  | And LTL LTL
  | Or LTL LTL
  | Implies LTL LTL
  | X LTL            -- Next
  | G LTL            -- Globally/Always
  | F LTL            -- Eventually
  | U LTL LTL        -- Until
  deriving (Eq, Show)

-- | Sugar
(&&&) = And
(|||) = Or
(-->) = Implies

-- Example in paper
exampleLtlFormula :: LTL
exampleLtlFormula = G ( AP "r" ||| X (AP "g"))

waterTankExampleLtlFormula = G (AP "level > 0") &&& G (AP "level < 100")
   -- TOOD &&& G ((AP "open" &&& X (AP "close")) --> (X X (AP "close") &&& XXX (AP "close")))

-- | A trace I think?
type Trace = [Set Prop]

-- | Does the trace satisfy the LTL
-- TODO LLM generated might be wrong. This tracks the index but I think we can write this recursively?
satisfies :: Trace -> Int -> LTL -> Bool
satisfies σ idx formula = case formula of
  AP p ->
    idx < length σ && p `elem` (σ !! idx)
  Not f ->
    not (satisfies σ idx f)
  And f1 f2 ->
    satisfies σ idx f1 && satisfies σ idx f2
  Or f1 f2 ->
    satisfies σ idx f1 || satisfies σ idx f2
  Implies f1 f2 ->
    if satisfies σ idx f1 then satisfies σ idx f2 else True
  X f ->
    satisfies σ (idx + 1) f
  G f ->
    all (\i -> satisfies σ i f) [idx .. length σ - 1]
  F f ->
    any (\i -> satisfies σ i f) [idx .. length σ - 1]
  U f1 f2 ->
    let future = drop idx σ
        holdsAt i = satisfies σ i f2 && all (\j -> satisfies σ j f1) [idx .. i - 1]
    in any (\i -> holdsAt i) [idx .. length σ - 1]

-- | Preemptive Shield iteration
-- Given the time step compute a set of safe actions (remove unsafe actions)
-- Environment executes one action and moves to the next state providing a reward
-- I think the paper describes this more clearly even though this might be harder to use
-- The input alphabet Σᵢ = Σᵢ¹ x Σᵢ² = L x A
-- The output alphabet Σₒ = 2ᴬ
-- Where A is the boolean 'Actions' in the MDP
-- preemptiveShieldIter :: (L, A) -> Set A
-- preemptiveShieldIter (l, a) = undefined

-- Label set e.g. {level < 1, 1 ≤ level ≤ 99, level > 99}
type L = Set Prop


-- | Water Tank Example
watertankL :: L
watertankL = Set.fromList ["level < 1", "1 ≤ level ≤ 99", "level > 99"]

-- waterTankA :: A
-- waterTankA = Set.fromList [ "opened", "closed"]
