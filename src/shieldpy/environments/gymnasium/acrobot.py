from enum import Enum, auto
import gymnasium as gym
from shieldpy.environments.gymnasium.interface import bins, bins_to_enum, enum_to_bins
from shieldpy.automata.nondeterministic_finite import Transition, NFA

BINS_PER_DIM = 50
env = gym.make("Acrobot-v1")
bins = bins(env.observation_space, BINS_PER_DIM)
State = bins_to_enum(bins)
