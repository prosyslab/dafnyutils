"""Lightweight Dafny declaration kind values shared by protocol models."""

from enum import StrEnum


class DefinitionKind(StrEnum):
    CONSTANT = "constant"
    FUNCTION = "function"
    PREDICATE = "predicate"
    METHOD = "method"
    CONSTRUCTOR = "constructor"
    FUNCTION_BY_METHOD = "function-by-method"
    TWOSTATE_FUNCTION = "twostate function"
    TWOSTATE_PREDICATE = "twostate predicate"
    DATATYPE = "datatype"
