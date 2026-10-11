"""denote — a type-driven workbench for compositional model-theoretic semantics."""
__version__ = "0.1.0"

from .typesys import Type, Basic, Fun, E, T, S, V, D, parse_type, type_str
from .terms import show
from .parser import parse_term
from .typecheck import typecheck
from .reduce import normalize, canonical
from .trees import parse_tree, load_trees
from .lexicon import Lexicon
from .compose import Interpreter, Options
from .scope import readings, qr_lfs
from .models import Model, Evaluator, random_model
from .projection import project

__all__ = ["Type", "Basic", "Fun", "E", "T", "S", "V", "D", "parse_type", "type_str", "show",
           "parse_term", "typecheck", "normalize", "canonical", "parse_tree", "load_trees",
           "Lexicon", "Interpreter", "Options", "readings", "qr_lfs", "Model", "Evaluator",
           "random_model", "project", "__version__"]
