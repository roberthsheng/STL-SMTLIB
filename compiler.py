import re
from z3 import *

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
        ('NUMBER', r'\d+(\.\d*)?'),  
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
        if peek()[0] == expected_kind:
            index += 1
            return tokens[index - 1]
        else:
            raise ValueError(f'Expected {expected_kind} but got {peek()[0]}')

    # Parse an atomic expression
    def parse_atom():
        kind, value = peek()
        if kind == 'VAR':
            consume('VAR')
            return ('VAR', value)
        elif kind == 'NUMBER':
            consume('NUMBER')
            return ('NUMBER', int(value) if value.isdigit() else float(value))
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
    def parse_until():
        consume('LSQB')
        start_time = parse_term()
        consume('COMMA')
        end_time = parse_term()
        consume('RSQB')

        first_condition = parse_expression()
        consume('UNTIL')
        second_condition = parse_expression()

        return ('UNTIL', start_time, end_time, first_condition, second_condition)

    # Parse an expression
    def parse_expression():
        if peek()[0] == 'LSQB':
            return parse_until()
        else:
            return parse_boolean()

    # Start parsing
    return parse_expression()

def translate(node):
    kind = node[0]
    if kind == 'NUMBER':
        return str(node[1])
    elif kind == 'VAR':
        return node[1]
    elif kind == 'PLUS':
        _, left, right = node
        left_code = translate(left)
        right_code = translate(right)
        return f'(add {left_code} {right_code})'
    elif kind == 'GEQ':
        _, left, right = node
        left_code = translate(left)
        right_code = translate(right)
        return f'(>= {left_code} {right_code})'
    elif kind == 'BOOL_OP':
        if node[1] == '⊤':
            return 'true'
        elif node[1] == '⊥':
            return 'false'
        op, left, right = node[1:]
        left_code = translate(left)
        right_code = translate(right)
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
        expr_code = translate(expr)
        return f'(not {expr_code})'
    elif kind == 'UNTIL':
        start_time, end_time, first_condition, second_condition = node[1:]
        start_time_code = translate(start_time)
        end_time_code = translate(end_time)
        first_condition_code = translate(first_condition)
        second_condition_code = translate(second_condition)
        return f'(exists ((k Int)) (and (>= k {start_time_code}) (<= k {end_time_code}) (forall ((l Int)) (and (>= l 0) (< l k) {first_condition_code})) {second_condition_code}))'


def test_stl_to_smtlib():
    tests = [
        ("⊤", "true"), 
        ("⊥", "false"), 
        ("¬x", "(not x)"), 
        ("¬(x ∧ y)", "(not (and x y))"), 
        ("⊤ ∨ x", "(or true x)"), 
        ("⊥ ∧ x", "(and false x)"), 
        ("¬(⊤ ∨ x)", "(not (or true x))"),
        ("¬(⊥ ∧ x)", "(not (and false x))"),
        ("[0, 10] (x ≥ 3) U (y ≥ 5)", "(exists ((k Int)) (and (>= k 0) (<= k 10) (forall ((l Int)) (and (>= l 0) (< l k) (>= x 3))) (>= y 5)))"),
        ("[2, 5] (a + b ≥ 4) U (c ≥ 2)", "(exists ((k Int)) (and (>= k 2) (<= k 5) (forall ((l Int)) (and (>= l 0) (< l k) (>= (add a b) 4))) (>= c 2)))"),
        ("[0, 10] (x ≥ 3) U (y ≥ 5) ∧ (z ≥ 2)", "(exists ((k Int)) (and (>= k 0) (<= k 10) (forall ((l Int)) (and (>= l 0) (< l k) (>= x 3))) (and (>= y 5) (>= z 2))))"),
        ("[0, 10] (y ≥ 5) ∧ (z ≥ 2) U (x ≥ 3)", "(exists ((k Int)) (and (>= k 0) (<= k 10) (forall ((l Int)) (and (>= l 0) (< l k) (and (>= y 5) (>= z 2)))) (>= x 3)))"),
        ("[0, 10] ¬(y ≥ 5) ∧ ⊤ U ⊥", "(exists ((k Int)) (and (>= k 0) (<= k 10) (forall ((l Int)) (and (>= l 0) (< l k) (and (not (>= y 5)) true))) false))")
    ]

    for stl, expected_smtlib in tests:
        smtlib = stl_to_smtlib(stl)
        assert smtlib == expected_smtlib, f'Expected {expected_smtlib}, but got {smtlib}'
        
    print("All tests passed!")

test_stl_to_smtlib()