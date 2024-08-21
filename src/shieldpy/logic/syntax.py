from enum import Enum, auto
from dataclasses import dataclass
from typing import Union, Set


class Operator(Enum):
    AND = auto()
    OR = auto()
    NOT = auto()
    IMPLIES = auto()
    UNTIL = auto()


@dataclass(frozen=True)
class Atom:
    name: str


@dataclass(frozen=True)
class UnaryOp:
    op: Operator
    sub: "LTLFormula"


@dataclass(frozen=True)
class BinaryOp:
    op: Operator
    left: "LTLFormula"
    right: "LTLFormula"


@dataclass(frozen=True)
class TrueConstant:
    pass


LTLFormula = Union[Atom, UnaryOp, BinaryOp, TrueConstant]


# Convenience functions for creating LTL formulas
def atom(name: str) -> Atom:
    return Atom(name)


def true() -> TrueConstant:
    return TrueConstant()


def not_(sub: LTLFormula) -> UnaryOp:
    return UnaryOp(Operator.NOT, sub)


def and_(left: LTLFormula, right: LTLFormula) -> BinaryOp:
    return BinaryOp(Operator.AND, left, right)


def or_(left: LTLFormula, right: LTLFormula) -> BinaryOp:
    return BinaryOp(Operator.OR, left, right)


def implies(left: LTLFormula, right: LTLFormula) -> BinaryOp:
    return BinaryOp(Operator.IMPLIES, left, right)


def until(left: LTLFormula, right: LTLFormula) -> BinaryOp:
    return BinaryOp(Operator.UNTIL, left, right)


# Derived operators
def false() -> UnaryOp:
    return not_(true())


def eventually(sub: LTLFormula) -> BinaryOp:
    return until(true(), sub)


def always(sub: LTLFormula) -> UnaryOp:
    return not_(eventually(not_(sub)))


def next_(sub: LTLFormula) -> BinaryOp:
    return until(false(), sub)


def get_atoms(formula: LTLFormula) -> Set[str]:
    if isinstance(formula, Atom):
        return {formula.name}
    elif isinstance(formula, UnaryOp):
        return get_atoms(formula.sub)
    elif isinstance(formula, BinaryOp):
        return get_atoms(formula.left) | get_atoms(formula.right)
    elif isinstance(formula, TrueConstant):
        return set()
    raise ValueError(f"Unexpected formula type: {type(formula)}")


def to_repr(formula: LTLFormula) -> str:
    match formula:
        case Atom(name):
            return name
        case UnaryOp(Operator.NOT, sub):
            return f"!({to_repr(sub)})"
        case BinaryOp(op, left, right):
            left_str = to_repr(left)
            right_str = to_repr(right)
            match op:
                case Operator.AND:
                    return f"({left_str} & {right_str})"
                case Operator.OR:
                    return f"({left_str} | {right_str})"
                case Operator.IMPLIES:
                    return f"({left_str} -> {right_str})"
                case Operator.UNTIL:
                    return f"({left_str} U {right_str})"
                case _:
                    raise ValueError(f"Unexpected operator: {op}")
        case TrueConstant():
            return "true"
        case _:
            raise ValueError(f"Unexpected formula type: {type(formula)}")


def pretty_print(formula: LTLFormula) -> str:
    match formula:
        case Atom(name):
            return name
        case TrueConstant():
            return "true"
        case UnaryOp(
            Operator.NOT,
            BinaryOp(Operator.UNTIL, TrueConstant(), UnaryOp(Operator.NOT, sub)),
        ):
            return f"G({pretty_print(sub)})"
        case BinaryOp(Operator.UNTIL, TrueConstant(), sub):
            return f"F({pretty_print(sub)})"
        case BinaryOp(Operator.UNTIL, UnaryOp(Operator.NOT, TrueConstant()), sub):
            return f"X({pretty_print(sub)})"
        case UnaryOp(Operator.NOT, sub):
            return f"!({pretty_print(sub)})"
        case BinaryOp(Operator.AND, left, right):
            return f"({pretty_print(left)} & {pretty_print(right)})"
        case BinaryOp(Operator.OR, left, right):
            return f"({pretty_print(left)} | {pretty_print(right)})"
        case BinaryOp(Operator.IMPLIES, left, right):
            return f"({pretty_print(left)} -> {pretty_print(right)})"
        case BinaryOp(Operator.UNTIL, left, right):
            return f"({pretty_print(left)} U {pretty_print(right)})"
        case _:
            return to_repr(formula)
