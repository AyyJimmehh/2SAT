import ply.lex as lex
import ply.yacc as yacc

tokens = (
    'VAR',
    'CONJUNCTION', 'DISJUNCTION', 'IMPLICATION', 'NEGATION',
    'LPAREN', 'RPAREN'
)

# Tokens
t_VAR = r'[a-z]'
t_CONJUNCTION = r'/\\'
t_DISJUNCTION = r'\\/'
t_IMPLICATION = r'->'
t_NEGATION = r'~'
t_LPAREN = r'\('
t_RPAREN = r'\)'

# Ignored characters
t_ignore = ' \t'


def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)


lex.lex()


# Grammar
def p_expression_conjunction(p):
    'expression : expression CONJUNCTION expression'
    p[0] = [p[1], p[3]]


def p_expression_paren(p):
    'expression : LPAREN expression RPAREN'
    p[0] = p[2]


def p_expression_clause(p):
    'expression : clause'
    p[0] = p[1]


def p_clause_implication(p):
    'clause : literal IMPLICATION literal'
    if p[1].startswith('~'):
        p[0] = [p[1][1:], p[3]]
    else:
        p[0] = ['~' + p[1], p[3]]


def p_clause_disjunction(p):
    'clause : literal DISJUNCTION literal'
    p[0] = [p[1], p[3]]


def p_clause_unit(p):
    'clause : literal'
    p[0] = [p[1]]


def p_lit_negation(p):
    'literal : NEGATION literal'
    p[0] = p[1] + p[2]


def p_lit_var(p):
    'literal : VAR'
    p[0] = p[1]


def p_error(p):
    print("Syntax error at '%s'" % p.value)


parser = yacc.yacc()


def flatten(lst):
    if isinstance(lst[0], list) and isinstance(lst[1], list) and len(lst[0]) == 1:
        yield lst[0]
        yield from flatten(lst[1])
    elif isinstance(lst[0], list) and isinstance(lst[1], list):
        yield from flatten(lst[0])
        yield from flatten(lst[1])
    elif isinstance(lst[0], list) and isinstance(lst[1], lst) and len(lst[1]) == 1:
        yield from flatten(lst[0])
        yield lst[1]
    else:
        yield lst


def is_tautology(clause):
    for literal1 in clause:
        for literal2 in clause:
            if literal1 == f"~{literal2}":
                return True
    return False


def has_duplicate_literals(clause):
    literals = set()
    for literal in clause:
        if literal in literals or f"~{literal}" in literals:
            return True
        literals.add(literal)
    return False


def resolve(clause1, clause2):
    new_clause = []

    for literal1 in clause1:
        for literal2 in clause2:
            if literal1 == f"~{literal2}" or literal2 == f"~{literal1}":
                new_clause.extend(
                    [lit for lit in clause1 if lit != literal1] + [lit for lit in clause2 if lit != literal2])
                return new_clause


def is_satisfiable(cnf):
    cnf = list(flatten(parser.parse(cnf)))
    new_clauses = [clause for clause in cnf if
                   not is_tautology(clause) and not has_duplicate_literals(clause)]  # Remove tautologies and duplicates
    visited = set(map(lambda c: tuple(sorted(c)), new_clauses))  # Keep track of visited clauses

    while True:
        new_clause_added = False  # Track if any new clause is added in this iteration
        for i in range(len(new_clauses)):
            for j in range(i + 1, len(new_clauses)):
                clause1 = new_clauses[i]
                clause2 = new_clauses[j]
                resolvent = resolve(clause1, clause2)
                if resolvent:
                    sorted_resolvent = tuple(sorted(resolvent))
                    if sorted_resolvent not in visited and not is_tautology(resolvent) and not has_duplicate_literals(
                            resolvent):
                        visited.add(sorted_resolvent)
                        new_clauses.append(resolvent)
                        new_clause_added = True
                        if (len(resolvent) == 1 and f"~{resolvent[0]}" in new_clauses[-1]) or (
                                len(resolvent) == 1 and resolvent[0] in new_clauses[-1]):
                            return False  # Unsatisfiable
        if not new_clause_added:
            return True, new_clauses  # Satisfiable


def sat_assignment(cnf):
    variables = set()
    satisfying_assignment = {}
    r, resolution_clauses = is_satisfiable(cnf)
    cnf = list(flatten(parser.parse(cnf)))
    for clause in cnf:
        for literal in clause:
            variable = literal[1:] if literal[0] == "~" else literal
            variables.add(variable)

    for variable in variables:
        satisfying_assignment[variable] = False  # Initialize all variables to False

    for clause in resolution_clauses:
        for literal in clause:
            variable = literal[1:] if literal[0] == "~" else literal
            satisfying_assignment[variable] = not literal.startswith("~")

    # Check if the satisfying assignment satisfies the entire CNF
    for clause in cnf:
        clause_satisfied = False
        for literal in clause:
            variable = literal[1:] if literal[0] == "~" else literal
            if (literal.startswith("~") and not satisfying_assignment[variable]) or (
                    not literal.startswith("~") and satisfying_assignment[variable]):
                clause_satisfied = True
                break

    return satisfying_assignment
