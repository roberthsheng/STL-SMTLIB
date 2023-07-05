import re
from z3 import *
import tseitin

def stl_to_smtlib(stl_code):
    # Convert STL to tokens
    tokens = list(tokenize(stl_code))
    # Convert tokens to parse tree
    parse_tree = parse(tokens)
    # Convert parse tree to SMT-LIB
    smtlib_code = translate(parse_tree)
    return smtlib_code

def tokenize(expr):
    TOKEN_SPECIFICATION = [
        ('COEFF', r'\b\d+(\.\d+)?[a-zA-Z_][a-zA-Z_0-9]*\b(?<!U)'),
        ('NUMBER', r'\b\d+(\.\d*)?\b'),  
        ('VAR', r'[a-zA-Z_][a-zA-Z_0-9]*\b(?<!U)'),  # VAR cannot be U
        ('UNTIL', r'U'),  
        ('BOOL_OP', r'[∨∧]'),  
        ('ABS', r'[⊤⊥]'),
        ('NEG', r'¬'),  
        ('GEQ', r'≥'),  
        ('PLUS', r'\+'),
        ('LB', r'\('),  
        ('RB', r'\)'),  
        ('LSQB', r'\['),  
        ('RSQB', r'\]'),  
        ('COMMA', r','),  
        ('LOWER', r'(?<=\[)\d{1,6}(?=,)'),
        ('UPPER', r'(?<=,)\d{1,6}(?=\])'),
        ('WHITESPACE', r'\s+'),  
    ]

    tok_regex = '|'.join('(?P<%s>%s)' % pair for pair in TOKEN_SPECIFICATION)
    for mo in re.finditer(tok_regex, expr):
        kind = mo.lastgroup
        if kind != 'WHITESPACE':
            yield kind, mo.group(kind)

def parse(tokens):
    # Cursor
    index = 0

    # Peek at the next token in the stream
    def peek(n = 0):
        nonlocal index
        if index + n < len(tokens):
            return tokens[index + n]
        else:
            return ('EOF', None)

    # Consume the next token from the stream
    def consume(expected_kind):
        nonlocal index
        kind, value = peek()
        if kind == expected_kind or (kind == 'NUMBER' and expected_kind in ('LOWER', 'UPPER')):
            index += 1
            return kind, value
        else:
            raise ValueError(f'Expected {expected_kind} but got {kind}')

    # Parse an atomic expression
    def parse_atom():
        kind, value = peek()
        if kind == 'VAR':
            consume('VAR')
            return ('VAR', value)
        elif kind == 'NUMBER':
            consume('NUMBER')
            return ('NUMBER', int(value) if value.isdigit() else float(value))
        elif kind == 'COEFF':
            consume('COEFF')
            coeff, var = value[:-1], value[-1]
            return ('COEFF', (int(coeff) if coeff.isdigit() else float(coeff), var))
        elif kind == 'LB':
            consume('LB')
            expr = parse_expression()
            consume('RB')
            return expr
        elif kind == 'ABS':
            consume('ABS')
            if value == '⊤':
                return ('BOOL_OP', '⊤')
            elif value == '⊥':
                return ('BOOL_OP', '⊥')
        elif kind == 'NEG':
            consume('NEG')
            atom = parse_atom()
            return ('NOT', atom)
        else:
            raise ValueError(f'Unexpected {kind}')

    # Parse a term
    def parse_term():
        left = parse_atom()
        while peek() and peek()[0] == 'PLUS':
            op = consume('PLUS')[1]
            right = parse_atom()
            left = ('PLUS', left, right)
        return left

    # Parse an inequality
    def parse_inequality():
        left = parse_term()
        if peek()[0] == 'GEQ':
            consume('GEQ')
            right = parse_term()
            return ('GEQ', left, right)
        else:
            return left

    # Parse a boolean expression
    def parse_boolean():
        left = parse_inequality()
        while peek() and peek()[0] == 'BOOL_OP':
            op = consume('BOOL_OP')[1]
            right = parse_inequality()
            left = ('BOOL_OP', op, left, right)
        return left

    # Parse until
    def parse_until(first_condition):
        consume('UNTIL')

        consume('LSQB')
        start_time = consume('LOWER')
        consume('COMMA')
        end_time = consume('UPPER')
        consume('RSQB')

        second_condition = parse_expression()

        return ('UNTIL', start_time, end_time, first_condition, second_condition)


    # Parse an expression
    def parse_expression():
        left = parse_boolean()
        if peek()[0] == 'UNTIL':
            return parse_until(left)
        else:
            return left

    # Start parsing
    return parse_expression()

# def replace_vars_with_time(expr, time):
#     ignore_list = ['true', 'false', 'and', 'or', 'not']  # List of terms to ignore

#     # Find all words consisting only of alphabetical characters
#     words = re.findall('[a-zA-Z]+', expr)
#     # Find all words consisting of alphabetical characters followed by a number
#     words_with_time = re.findall('[a-zA-Z]+\d+', expr)

#     for word in words:
#         # Skip if word is in the ignore list
#         if word in ignore_list:
#             continue

#         # Replace each occurrence of the word in the expression with the word followed by the time value
#         expr = re.sub(r'\b' + word + r'\b', word + str(time), expr)
    
#     for word in words_with_time:
#         # Skip if word is in the ignore list
#         if word in ignore_list:
#             continue

#         # Replace each occurrence of the word in the expression with the word followed by the new time value, which is the number after the word plus the passed time
#         # get old time by stripping word of alphabetical characters
#         old_time = int(re.sub('[a-zA-Z]+', '', word))
#         # get new time by adding old time to passed time
#         new_time = old_time + time
#         # replace word with new word
#         expr = re.sub(r'\b' + word + r'\b', word[:-len(str(old_time))] + str(new_time), expr)

#     return expr

def translate(node, base_time=0):
    kind = node[0]
    if kind == 'NUMBER':
        return str(node[1])
    elif kind == 'VAR':
        return node[1] + str(base_time)
    elif kind == 'COEFF':
        coeff, var = node[1]
        return f'(* {coeff} {var}{base_time})'
    elif kind == 'PLUS':
        _, left, right = node
        left_code = translate(left, base_time)
        right_code = translate(right, base_time)
        return f'(+ {left_code} {right_code})'
    elif kind == 'GEQ':
        _, left, right = node
        left_code = translate(left, base_time)
        right_code = translate(right, base_time)
        return f'(>= {left_code} {right_code})'
    elif kind == 'BOOL_OP':
        if node[1] == '⊤':
            return 'true'
        elif node[1] == '⊥':
            return 'false'
        op, left, right = node[1:]
        left_code = translate(left, base_time)
        right_code = translate(right, base_time)
        if op == '∨':
            op = 'or'
        elif op == '∧':
            op = 'and'
        elif op == '⊤':
            return 'true'
        elif op == '⊥':
            return 'false'
        return f'({op} {left_code} {right_code})'
    elif kind == 'NOT':
        _, expr = node
        expr_code = translate(expr, base_time)
        return f'(not {expr_code})'
    elif kind == 'UNTIL':
        _, start_time, end_time, first_condition, second_condition = node
        start_time = int(translate(start_time, base_time))
        end_time = int(translate(end_time, base_time))
        
        or_expr = []
        for k in range(start_time, end_time + 1):
            and_expr = [translate(first_condition, base_time+l) for l in range(0, k)]
            or_expr.append(f'(and {" ".join(and_expr)} {translate(second_condition, base_time+k)})')

        return f'(or {" ".join(or_expr)})'


def test_stl_to_smtlib():
    tests = [
        # ("⊤"), 
        # ("⊥"), 
        # ("¬x"), 
        # ("x ∨ y"), 
        # ("x ∧ ¬y"), 
        # ("¬(x ∧ y)"), 
        # ("⊤ ∨ x"), 
        # ("⊥ ∧ x"), 
        # ("⊥ ∧ ⊥"), 
        # ("¬(⊤ ∨ x)"),
        # ("¬(⊥ ∧ x)"),
        # ("⊤ U[0, 5] ⊥"),
        # ("(x ≥ 3) U[1, 3] (z ≥ 2)"),
        ("((x ≥ 3) U[1, 2] (z ≥ 2)) U[3, 5] (y ≥ 5)"),
        # ("(x ≥ 3) U[3, 5] ((z ≥ 2) U[1, 2] (y ≥ 5))"),
        # ("(a U[1, 2] b) U[3, 5] c"),
        # ("(x ≥ 3) U[0, 10] (y ≥ 5)"),
        # ("(a + b ≥ 4) U[2, 4] (c ≥ 2)"),
        # ("(x ≥ 3) U[0, 10] (y ≥ 5) ∧ (z ≥ 2)"),
        # ("(y ≥ 5) ∧ (z ≥ 2) U[0, 10] (x ≥ 3)"),
        # ("¬(y ≥ 5) ∧ ⊤ U[0, 10] ⊥"),
        # ("2.95x ≥ 9"),
        # ("3x + 2y ≥ 9"),
        # ("(2a + b ≥ 4) U[2, 5] (3c ≥ 2)"),
        # ("2x ≥ 6 ∧ 3y ≥ 9"),
        # ("¬(4.5y ≥ 20) ∧ ⊤ U[0, 10] ⊥"),
        # ("1 ≥ 2")
    ]

    for stl in tests:
        smtlib = stl_to_smtlib(stl)
        print(stl)
        print(smtlib)
        formula = tseitin.tseitin_to_smt(smtlib)
        print(formula)

        print()

# test_stl_to_smtlib()