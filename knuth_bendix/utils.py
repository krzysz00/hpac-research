from matchpy import Expression, Substitution
from matchpy import substitute as _substitute


def substitute(term: Expression, substitution: Substitution) -> Expression:
    """Wrapper around :fn:`matchpy.substitute` that does a typecheck"""
    ret = _substitute(term, substitution)
    if not isinstance(ret, Expression):
        raise(ValueError("Unexpected list of expressions", ret, "from",
                         substitution, "on", term))
    return ret
