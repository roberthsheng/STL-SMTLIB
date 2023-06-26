import compiler, measures, tseitin, z3

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
    # ("((x ≥ 3) U[1, 2] (z ≥ 2)) U[3, 5] (y ≥ 5)"),
    # ("(x ≥ 3) U[3, 5] ((z ≥ 2) U[1, 2] (y ≥ 5))"),
    # ("(a U[1, 2] b) U[3, 5] c"),
    # ("(x ≥ 3) U[0, 10] (y ≥ 5)"),
    ("(a + b ≥ 4) U[2, 4] (c ≥ 2)"),
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
    print(stl)
    smtlib = compiler.stl_to_smtlib(stl)
    formula = tseitin.tseitin_to_smt(smtlib)
    # print(formula)
    # print(tseitin.cnf_to_z3(transformed))
    # tseitin.evaluate(transformed, mapping)

    measures.all_clauses(formula, 'smt/clauses.smt2')

    # use z3 to check satisfiability
    s1 = z3.Solver()
    # formula is in clauses.smt2
    s1.from_file('smt/clauses.smt2')
    print('s1', formula)
    print(s1.check())
    if s1.check() == z3.sat:
        print(s1.model())
    
    print()
    not_formula = tseitin.tseitin_to_smt('(not ' + smtlib + ')')
    measures.all_clauses(not_formula, 'smt/not_clauses.smt2')
    print('s2', not_formula)
    s2 = z3.Solver()
    s2.from_file('smt/not_clauses.smt2')
    print(s2.check())
    if s2.check() == z3.sat:
        print(s2.model())



    # if s1.check() == z3.sat and s2.check() == z3.sat:
    #     print("inconclusive")
    # elif s2.check() == z3.unsat:
    #     print("True")
    # elif s1.check() == z3.unsat:
    #     print("False")

    print()
