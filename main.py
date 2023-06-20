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
    transformed, mapping = tseitin.tseitin_to_cnf(smtlib)
    formula = tseitin.cnf_to_smt(transformed)
    print(formula)
    # print(tseitin.cnf_to_z3(transformed))
    # tseitin.evaluate(transformed, mapping)

    measures.all_clauses(formula)

    # use z3 to check satisfiability
    s = z3.Solver()
    # formula is in clauses.smt2
    s.from_file('smt/clauses.smt2')
    print(s.check())
    if s.check() == z3.sat:
        print(s.model())


    print()
