import copy
import sys
import re


class DPLL:
    # assignment element. either implied (by clause) or decision
    class AssignmentElem:
        def __init__(self, truth_val, imply_clause):
            self.truth_val = truth_val
            self.imply_clause = imply_clause

        def __str__(self):
            # return f"truth_val: {self.truth_val}, imply_clause: {self.imply_clause}"
            return f"{self.truth_val}"

    # parse cnf formula from input file
    def __init__(self):
        # read file
        if len(sys.argv) < 2:
            sys.exit(1)

        filename = sys.argv[1]

        with open(filename, "r") as f:
            data = f.read()

        cnf_formula = set()
        acc_literal_lst = []
        num_vars, num_clauses = 0, 0

        # parse
        for line in data.splitlines():
            if line.isspace() or len(line) == 0:
                continue
            elif re.search("^c.*", line):
                continue
            elif match_pcnf := re.search(r"^p cnf (\d+) (\d+)", line):
                num_vars = int(match_pcnf.group(1))
                num_clauses = int(match_pcnf.group(2))
            else:
                literal_lst = [int(x) for x in re.findall(r"-?\d+", line)]
                acc_literal_lst = acc_literal_lst + literal_lst
                if 0 in acc_literal_lst:
                    acc_literal_lst.remove(0)
                    cnf_formula.add(frozenset(acc_literal_lst))
                    acc_literal_lst = []

        # infornations
        self.num_vars, self.num_clauses = num_vars, num_clauses
        # store cnf_formula
        self.cnf_formula = cnf_formula
        # prop_var|-> assignment_elem
        self.const_assignment = {}
        self.assignment = {}
        # f_a
        self.f_a = {}
        # prop_var|-> clauses which contain prop_var
        self.prop_clauses_map = {}

    # dpll algorithm
    def dpll(self):
        if not self.prune():
            return None
        self.init_prop_clauses_map()
        self.init_f_a()
        while True:
            self.unit_prop()
            if self.satisfied():
                return self.const_assignment, self.assignment
            elif conflict_clause := self.find_conflict_clause():
                clause = self.learn(conflict_clause)
                self.add_clause(clause)
                print(f"after learn. formula size: {len(self.cnf_formula)}")
                if len(clause) == 0:
                    return None
                while not self.is_unit_clause(clause):
                    self.pop_assignment()
            else:
                for i in range(1, self.num_vars + 1):
                    if i in self.assignment.keys() or i in self.const_assignment.keys():
                        continue
                    print("decision", end=" ")
                    self.add_assignment(i, self.AssignmentElem(False, None))
                    break

    def unit_prop(self):
        while res := self.find_unit_clause():
            prop_var, truth_val, imply_clause = res
            self.add_assignment(prop_var, self.AssignmentElem(truth_val, imply_clause))

    def learn(self, conflict_clause):
        k = len(self.assignment)

        # prop_vars[1]: firstly inserted to assignment, prop_vars[2]: p2 secondly inserted to assignment
        prop_vars = [0] + [p for p in self.assignment.keys()]

        # Dk+1 = conflict_clause
        D = conflict_clause
        for i in reversed(range(1, k + 1)):
            pi = prop_vars[i]
            if self.assignment[pi].imply_clause is None or (
                pi not in D and -pi not in D
            ):
                continue
            if self.assignment[pi].imply_clause and (pi in D or -pi in D):
                # for literal in self.assignment[pi].imply_clause:
                #     if prop_vars.index(abs(literal)) > i:
                #         print(f"prop_vars: {prop_vars}")
                #         print(f"pi: {pi}, i: {i}")
                #         for literal in self.assignment[pi].imply_clause:
                #             print(
                #                 f"{literal}: index {prop_vars.index(abs(literal))}",
                #                 end=", ",
                #             )
                #         print("")
                #         0 / 0
                D = self.resolve(self.assignment[pi].imply_clause, D, pi)

        return D

    # util functions
    def add_clause(self, clause):
        self.cnf_formula.add(clause)
        self.update_f_a_after_add_clause(clause)

    def add_assignment(self, prop_var, assignment_elem):
        self.assignment[prop_var] = assignment_elem
        self.update_f_a_after_add(prop_var, assignment_elem)

        print(f"add. {prop_var}: {assignment_elem}, len: {len(self.assignment)}")

    def pop_assignment(self):
        prop_var, assignment_elem = self.assignment.popitem()
        self.update_f_a_after_pop(prop_var, assignment_elem)

        print(f"pop. {prop_var}: {assignment_elem}, len: {len(self.assignment)}")

    def is_unit_clause(self, clause):
        tmp_clause = set(clause)
        for prop_var, assign_elem in self.assignment.items():
            literal_assigned_false = -prop_var if assign_elem.truth_val else prop_var
            if literal_assigned_false in tmp_clause:
                tmp_clause.remove(literal_assigned_false)
        if len(tmp_clause) == 1:
            return True
        else:
            return False

    def find_unit_clause(self):
        for full_clause, clause in self.f_a.items():
            if clause is None or not len(clause) == 1:
                continue
            imply_clause = full_clause
            literal = set(clause).pop()

            return abs(literal), (True if literal > 0 else False), imply_clause

        return None

    def find_conflict_clause(self):
        for full_clause, clause in self.f_a.items():
            if clause is None:
                continue
            if len(clause) == 0:
                return full_clause
        return None

    def satisfied(self):
        for full_clause, clause in self.f_a.items():
            if clause is not None:
                return False
        return True

    def prune(self):
        # key: prop_var, value: clause set pointer <- if change in one place, changed in other place
        print("before prune")
        print(self.cnf_formula)
        prop_mut_clauses_map = {}
        cnf_formula_lst = [set(clause) for clause in self.cnf_formula]

        for clause in cnf_formula_lst:
            for literal in clause:
                prop_var = abs(literal)
                if not prop_var in prop_mut_clauses_map:
                    prop_mut_clauses_map[prop_var] = list()
                prop_mut_clauses_map[prop_var].append(clause)

        true_literals = []
        unit_literal_stack = []
        for clause in self.cnf_formula:
            if len(clause) == 1:
                literal = set(clause).pop()
                self.const_assignment[abs(literal)] = self.AssignmentElem(
                    True if literal > 0 else False, None
                )
                true_literals.append(literal)
                unit_literal_stack.append(literal)

        # clause에서 false로 assign된 literal 지움
        while len(unit_literal_stack) > 0:
            unit_literal = unit_literal_stack.pop()
            prop_var = abs(unit_literal)
            for clause in prop_mut_clauses_map[prop_var]:
                if -unit_literal in clause:
                    clause.remove(-unit_literal)
                    if len(clause) == 1:
                        literal = list(clause)[0]
                        self.const_assignment[abs(literal)] = self.AssignmentElem(
                            True if literal > 0 else False, None
                        )
                        true_literals.append(literal)
                        unit_literal_stack.append(literal)

        # true literal을 포함한 clause를 지움
        cnf_formula = set()
        for clauses in prop_mut_clauses_map.values():
            for clause in clauses:
                cnf_formula.add(frozenset(clause))
                for literal in clause:
                    if literal in true_literals:
                        cnf_formula.remove(frozenset(clause))
                        break

        self.cnf_formula = set()
        for clause in cnf_formula:
            if len(clause) == 0:
                # unsat
                return False
            elif not len(clause) == 1:
                self.cnf_formula.add(clause)
        print("after prune")
        print(self.cnf_formula)
        return True

    def init_f_a(self):
        for clause in self.cnf_formula:
            self.f_a[clause] = clause

    def init_prop_clauses_map(self):
        for clause in self.cnf_formula:
            for literal in clause:
                prop_var = abs(literal)
                if not prop_var in self.prop_clauses_map:
                    self.prop_clauses_map[prop_var] = set()
                self.prop_clauses_map[prop_var].add(clause)

    def update_f_a_after_add(self, prop_var, assign_elem):
        true_literal = prop_var if assign_elem.truth_val else -prop_var
        false_literal = -prop_var if assign_elem.truth_val else prop_var

        target_clauses = self.prop_clauses_map[prop_var]
        for full_clause in target_clauses:
            clause = self.f_a[full_clause]
            if clause is None:
                continue
            if true_literal in clause:
                self.f_a[full_clause] = None
            elif false_literal in clause:
                tmp_clause = set(clause)
                tmp_clause.remove(false_literal)
                self.f_a[full_clause] = frozenset(tmp_clause)

    def update_f_a_after_pop(self, prop_var, assign_elem):
        true_literal = prop_var if assign_elem.truth_val else -prop_var
        false_literal = -prop_var if assign_elem.truth_val else prop_var
        literal_assigned_false_lst = [
            (-prop_var if assign_elem.truth_val else prop_var)
            for prop_var, assign_elem in self.assignment.items()
        ]

        target_clauses = self.prop_clauses_map[prop_var]
        for full_clause in target_clauses:
            if true_literal in full_clause:
                if not self.has_true(full_clause):
                    tmp_clause = set(full_clause)
                    for literal in full_clause:
                        if literal in literal_assigned_false_lst:
                            tmp_clause.remove(literal)
                    self.f_a[full_clause] = frozenset(tmp_clause)
            elif false_literal in full_clause:
                clause = self.f_a[full_clause]
                if clause is None:
                    continue
                tmp_clause = set(clause)
                tmp_clause.add(false_literal)
                self.f_a[full_clause] = frozenset(tmp_clause)

    def update_f_a_after_add_clause(self, clause):
        for literal in clause:
            prop_var = abs(literal)
            self.prop_clauses_map[prop_var].add(clause)

        literal_assigned_true_lst = [
            (prop_var if assign_elem.truth_val else -prop_var)
            for prop_var, assign_elem in self.assignment.items()
        ]
        literal_assigned_false_lst = [
            (-prop_var if assign_elem.truth_val else prop_var)
            for prop_var, assign_elem in self.assignment.items()
        ]

        tmp_clause = set(clause)
        for literal in clause:
            if literal in literal_assigned_true_lst:
                self.f_a[clause] = None
                return
            elif literal in literal_assigned_false_lst:
                tmp_clause.remove(literal)
        self.f_a[clause] = frozenset(tmp_clause)

    def has_true(self, clause):
        literal_assigned_true_lst = [
            (prop_var if assign_elem.truth_val else -prop_var)
            for prop_var, assign_elem in self.assignment.items()
        ]
        for literal in clause:
            if literal in literal_assigned_true_lst:
                return True
        return False

    def resolve(self, c, d, pi):
        tmp_c = set(c)
        tmp_d = set(d)
        if pi in tmp_c:
            tmp_c.remove(pi)
            tmp_d.remove(-pi)
        else:
            tmp_c.remove(-pi)
            tmp_d.remove(pi)

        union = tmp_c.union(tmp_d)
        return frozenset(union)


if __name__ == "__main__":
    dpll = DPLL()
    res = dpll.dpll()
    if res:
        print("s SATISFIABLE")
        assignment_lst = [
            (prop_var if assignment_elem.truth_val else -prop_var)
            for prop_var, assignment_elem in res[0].items()
        ]
        assignment_lst = assignment_lst + [
            (prop_var if assignment_elem.truth_val else -prop_var)
            for prop_var, assignment_elem in res[1].items()
        ]
        output = (
            "v " + " ".join(str(assignment) for assignment in assignment_lst) + " 0"
        )
        print(output)
    else:
        print("s UNSATISFIABLE")
