import re
from enum import Enum
from typing import Any, Dict, Tuple
import gymnasium as gym
import numpy as np
from shieldpy.automata.dynamic_nondeterministic_finite import (
    DynamicNFA,
    State,
    Alphabet,
)


class DynNFAGymWrapper(gym.Wrapper):
    def __init__(self, env: gym.Env, nfa: DynamicNFA):
        super().__init__(env)
        self.nfa = nfa
        self.current_states = {self.nfa.start}
        self.step_count = 0

    def gymstate_to_nfastate(self, gym_state: Any) -> State:
        # Convert gym_state to a hashable representation
        if isinstance(gym_state, np.ndarray):
            # Round to reduce the number of unique states
            # and convert to tuple for hashability
            return State(tuple(np.round(gym_state, decimals=2)))
        elif isinstance(gym_state, (int, float)):
            return State(np.round(gym_state, decimals=4))
        else:
            # For more complex states, you might need a custom solution
            return State(str(gym_state))

    def gymaction_to_nfasymbol(self, gym_action: Any) -> Alphabet:
        # This method needs to be implemented based on your specific mapping
        # For now, we'll use a simple string representation
        return Alphabet(str(gym_action))

    def reset(self, **kwargs) -> Tuple[Any, Dict]:
        obs, info = self.env.reset(**kwargs)
        self.current_states = {self.nfa.start}
        self.step_count = 0
        return obs, info

    def step(self, action: Any) -> Tuple[Any, float, bool, bool, Dict]:
        # Perform step in the wrapped environment
        obs, reward, terminated, truncated, info = self.env.step(action)

        # Convert Gym action to NFA symbol
        nfa_symbol = self.gymaction_to_nfasymbol(action)

        # Convert Gym state to NFA state
        nfa_state = self.gymstate_to_nfastate(obs)

        # Update NFA states
        next_states = set()
        for current_state in self.current_states:
            # Add transition if it doesn't exist
            self.nfa.add_transition(current_state, nfa_symbol, nfa_state)
            next_states.update(self.nfa.get_next_states(current_state, nfa_symbol))

        self.current_states = next_states

        # Check if we've reached an accept state in the NFA
        nfa_terminated = any(state in self.nfa.accept for state in self.current_states)

        # Terminate if either the environment or the NFA says so
        terminated = terminated or nfa_terminated

        # You might want to modify the reward based on the NFA states
        # reward = self.modify_reward(reward, self.current_states)

        self.step_count += 1

        return obs, reward, terminated, truncated, info

    def set_accept_state(self, gym_state: Any):
        nfa_state = self.gymstate_to_nfastate(gym_state)
        self.nfa.set_accept_state(nfa_state)


def bins(obs_space: gym.spaces.Box, num: int) -> np.ndarray:
    low: np.ndarray = obs_space.low
    high: np.ndarray = obs_space.high
    return np.linspace(low, high, num)


def bins_to_enum(bins: np.ndarray) -> Enum:
    return Enum("Bins", {f"s_{i}{j}": f"s_{i}{j}" for i in bins for j in bins[i]})


def extract_tuple(s: str) -> tuple[int, int] | None:
    pattern = r"dim(\d+)_bin(\d+)"
    match = re.match(pattern, s)
    if match:
        i, j = map(int, match.groups())
        return (i, j)
    return None


def enum_to_bins(enum: Enum, bins: np.ndarray) -> np.ndarray | None:
    t = extract_tuple(enum.name)
    if t:
        return bins[t[0], t[1]]
    return None


def discrete_space_to_enum(
    space: gym.spaces.Discrete, name: str = "DiscreteSpace"
) -> Enum:
    return Enum(name, [f"action{i}" for i in range(space.n)])
