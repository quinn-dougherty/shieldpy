import pytest
import gymnasium as gym
import numpy as np
from gymnasium import spaces

from shieldpy.environments.gymnasium.interface import DynNFAGymWrapper
from shieldpy.automata.dynamic_nondeterministic_finite import (
    DynamicNFA,
    State,
    Alphabet,
)


class DummyEnv(gym.Env):
    def __init__(self):
        self.observation_space = spaces.Box(
            low=-1, high=1, shape=(4,), dtype=np.float32
        )
        self.action_space = spaces.Discrete(2)
        self.state = np.zeros(4)

    def reset(self):
        self.state = self.observation_space.sample()
        return self.state, {}

    def step(self, action):
        self.state = self.observation_space.sample()
        reward = 1.0 if np.all(np.abs(self.state) < 0.5) else 0.0
        done = False
        return self.state, reward, done, False, {}


@pytest.fixture
def wrapped_env():
    env = DummyEnv()
    nfa = DynamicNFA()
    return DynNFAGymWrapper(env, nfa)


def test_initialization(wrapped_env):
    assert isinstance(wrapped_env.env, DummyEnv)
    assert isinstance(wrapped_env.nfa, DynamicNFA)
    assert wrapped_env.current_states == {wrapped_env.nfa.start}
    assert wrapped_env.step_count == 0


def test_reset(wrapped_env):
    wrapped_env.step_count = 10
    wrapped_env.current_states = {State("some_state")}
    obs, info = wrapped_env.reset()
    assert wrapped_env.step_count == 0
    assert wrapped_env.current_states == {wrapped_env.nfa.start}
    assert obs.shape == (4,)
    assert isinstance(info, dict)


def test_gymstate_to_nfastate(wrapped_env):
    gym_state = np.array([0.1, -0.2, 0.3, -0.4])
    nfa_state = wrapped_env.gymstate_to_nfastate(gym_state)
    assert isinstance(nfa_state, State)
    if not isinstance(nfa_state.name, tuple):
        assert nfa_state.name.startswith("s0")  # Assuming step_count is 0


def test_gymaction_to_nfasymbol(wrapped_env):
    gym_action = 1
    nfa_symbol = wrapped_env.gymaction_to_nfasymbol(gym_action)
    assert isinstance(nfa_symbol, Alphabet)
    assert nfa_symbol.symbol == "1"


def test_step(wrapped_env):
    initial_state = wrapped_env.current_states
    obs, reward, terminated, truncated, info = wrapped_env.step(1)
    assert obs.shape == (4,)
    assert isinstance(reward, float)
    assert isinstance(terminated, bool)
    assert isinstance(truncated, bool)
    assert isinstance(info, dict)
    assert wrapped_env.step_count == 1
    assert wrapped_env.current_states != initial_state


def test_set_accept_state(wrapped_env):
    gym_state = np.zeros(4)
    wrapped_env.set_accept_state(gym_state)
    nfa_state = wrapped_env.gymstate_to_nfastate(gym_state)
    assert nfa_state in wrapped_env.nfa.accept


@pytest.mark.skip("idk")
def test_termination_on_accept_state(wrapped_env):
    # Set the zero state as an accept state
    zero_state = np.zeros(4)
    wrapped_env.set_accept_state(zero_state)

    # Force the environment to the zero state
    wrapped_env.env.state = zero_state

    # Step the environment
    _, _, terminated, _, _ = wrapped_env.step(0)

    # The episode should terminate because we reached an accept state
    assert terminated


def test_nfa_growth(wrapped_env):
    initial_transitions = len(wrapped_env.nfa.transitions)
    wrapped_env.step(0)
    assert len(wrapped_env.nfa.transitions) > initial_transitions
