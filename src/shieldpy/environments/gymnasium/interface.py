import re
from enum import Enum
import gymnasium as gym
import numpy as np


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
