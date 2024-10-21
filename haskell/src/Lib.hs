{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Lib where

import Data.Set (Set)

-- TODOs
-- Maybe start more top down instead so look at later pages and try to implement backwards.
-- I did the other approach and it was a bit harder to follow.
-- Maybe starting at preemptive shield which uses MDPs which then appl6y a shield to the actions (removing unsafe actions might make more sense)
-- OR do safety games but that's used in the above. If I struggle with the above I'll try this.


-- | Credits to TODO
-- Just guessing the types or stubbing them

-- | Unicode characters
-- You can setup latex input mode in emacs to use these
-- φ \varphi Specification
-- φˢ Safety automation
-- φᵐ MDP abstraction
-- Σ \Sigma Alphabet sometimes composed of the input and output alphabet Σ = Σᵢ x Σₒ
-- Σᵢ \Sigma_i Input alphabet
-- Σₒ \Sigma_o Output alphabet
-- δ \delta Transition function
-- ρ \rho
-- λ \lambda Output function
-- Gω G\omega Really G with a supper script omega
-- Many of these are described in section 3 Preliminaries

-- | MDP States
data S = S Int

-- | MDP Booleans
data A = A Bool

-- | Probablistic Transition Function
type P = (S, A) -> Set (S, Float)

-- | Reward funtion
type R = (S, A, S) -> Float


-- | Markov Decision Process
-- I wonder if we even need this given they start talking about an abstraction over the MDP φ
data M = M {
  _S :: Set S
  , sᵢ :: S -- Initial state
  , _A :: Set A -- Finite set of boolean actions
  , _P :: P
  , _R :: R
}

-- Automata States
data Q = Q Int deriving (Show, Eq, Ord)

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



-- Safety automation φˢ
-- The System S satisfies the automation if the run of S only visits safe states in F
data SafetyAutomation _Σᵢ¹ _Σᵢ² = SafetyAutomation {
  q :: Set Q -- States
  , q₀:: Q
  , _Σ :: _Σ
  , δ :: (Q, (_Σᵢ¹, _Σᵢ²)) -> Q
  , _F :: Set Q -- Set of safe states where F ⊆ Q
  }


-- | 2 player Game
-- G: TODO  Game states guessing that's a product of states from the environment and safety automation?
data Game G = Game {
    _G :: Set G -- Finite set of game states
    , q₀ :: G -- Initial state
    , δ :: (G, Σᵢ, Σₒ) -> G -- Transition function
    , win :: Gω

  
                 }

-- | Used for synthesizing the shield
-- Defines a set Fᵍ  ⊆ G of safe states
-- Where win(g₀, g₁, ...) iff ∀i ≥ 0. gᵢ ∈ Fᵍ
-- I think we can solve for this using SMT. In the original implementation they used BDDs.
-- safetyGame ∷ G -> G
-- safetyGame g = undefined


safetyGame ∷ S _Σᵢ¹ _Σᵢ² _Σ₀ -> SafetyAutomation -> S _ _
safetyGame=
    let g = undefined
        q = undefined
        _Σᵢ = undefined
        _Σₒ= undefined
        δ' = undefined -- (g, σᵢ ) = (g, σᵢ, ρ(g, σᵢ))
        ρ = undefined
    in undefined -- TODO S q _Σᵢ _Σₒ δ'
  -- | Uses the safety game to synthesize a shield which implements the winning strategy in a new reactive system (Is it a finite reactive system?)
-- shield  ∷ Shield _Σᵢ _Σ₀
-- shield =
--     let g = undefined
--         q = undefined
--         _Σᵢ = undefined
--         _Σₒ= undefined
--         δ' = undefined -- (g, σᵢ ) = (g, σᵢ, ρ(g, σᵢ))
--         ρ = undefined
--     in undefined -- TODO S q _Σᵢ _Σₒ δ'

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

-- This is actually properties of the shield maybe not what we want
-- But overall it can also be seem as transforming a MDP into a new MDP (section 5.1)
preemptiveShield :: M -> Shield -> M
preemptiveShield _M _S =
  -- Product of the original MDP and the state space of the shield
  let _S' = undefined
      -- For each s' in S' create a new subset of available actions
      -- Apply the shield to Aₛ to get A'ₛ
      -- So that gets us a bunch of A'ₛ but how do we get A'?
      _A' = undefined
      -- We only want transition functions from P for actions in A'ₛ
      _P' = undefined
      _R' = undefined
  in M _S' M.s_i  _A' _P' _R'

-- | Section 6 a shield is computed from an abstraction of the MDP φᵐ and the safety automaton φˢ
computeShield

-- Label set e.g. {level < 1, 1 ≤ level ≤ 99, level > 99}
type L = Set Prop


-- | Water Tank Example
watertankL :: L
watertankL = Set.fromList ["level < 1", "1 ≤ level ≤ 99", "level > 99"]

-- waterTankA :: A
-- waterTankA = Set.fromList [ "opened", "closed"]
