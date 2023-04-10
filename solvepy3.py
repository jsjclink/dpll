import sys
import re
import time


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
        self.assignment = {}

        self.start_time = time.time()
        self.unit_prop_time = 0.0
        self.learn_time = 0.0
        self.calculate_f_a_time = 0.0
        self.find_unit = 0.0
        self.update_f_a_time = 0.0

    # dpll algorithm
    def dpll(self):
        while True:
            # self.print_assignment()
            f_a = self.unit_prop()
            if len(f_a) == 0:
                return self.assignment
            elif frozenset() in f_a.keys():
                clause = self.learn(f_a[frozenset()])
                self.cnf_formula.add(clause)
                if len(clause) == 0:
                    return None
                while not self.is_unit_clause(clause):
                    self.pop_assignment()
            else:
                for i in range(1, self.num_vars + 1):
                    if i in self.assignment.keys():
                        continue
                    self.add_assignment(i, self.AssignmentElem(False, None))
                    break

    def unit_prop(self):
        start_time = time.time()

        f_a = self.calculate_f_a()
        while res := self.find_unit_clause_with_f_a(f_a):
            prop_var, truth_val, imply_clause = res
            self.add_assignment(prop_var, self.AssignmentElem(truth_val, imply_clause))
            f_a = self.update_f_a(f_a, prop_var, truth_val)

        self.unit_prop_time += time.time() - start_time

        return f_a

    def learn(self, conflict_clause):
        start_time = time.time()

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
                D = self.resolve(self.assignment[pi].imply_clause, D, pi)

        self.learn_time += time.time() - start_time

        return D

    # util functions
    def add_assignment(self, prop_var, assignment_elem):
        self.assignment[prop_var] = assignment_elem
        total = time.time() - self.start_time + 1.0
        print(
            f"add. {prop_var}: {assignment_elem}, len: {len(self.assignment)}, porp: {self.unit_prop_time / total * 100}%, learn: {self.learn_time / total * 100}%, calc_f_a: {self.calculate_f_a_time / total * 100}%, find_unit: {self.find_unit / total * 100}%, update_f_a: {self.update_f_a_time / total * 100}%"
        )

    def pop_assignment(self):
        prop_var, assignment_elem = self.assignment.popitem()
        total = time.time() - self.start_time + 1.0
        print(
            f"pop. {prop_var}: {assignment_elem}, len: {len(self.assignment)}, porp: {self.unit_prop_time / total * 100}%, learn: {self.learn_time / total * 100}%, calc_f_a: {self.calculate_f_a_time / total * 100}%, find_unit: {self.find_unit / total * 100}%, update_f_a: {self.update_f_a_time / total * 100}%"
        )

    def is_true_clause(self, clause):
        for prop_var, assign_elem in self.assignment.items():
            literal_assigned_true = prop_var if assign_elem.truth_val else -prop_var
            if literal_assigned_true in clause:
                return True
        return False

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

    def find_unit_clause_with_f_a(self, f_a):
        start_time = time.time()

        for clause in f_a.keys():
            if not len(clause) == 1:
                continue
            imply_clause = f_a[clause]
            tmp_clause = set(clause)
            literal = tmp_clause.pop()

            self.find_unit += time.time() - start_time

            return abs(literal), (True if literal > 0 else False), imply_clause

        self.find_unit += time.time() - start_time

        return None

    def calculate_f_a(self):
        start_time = time.time()

        f_a = {}
        for clause in self.cnf_formula:
            if self.is_true_clause(clause):
                continue
            tmp_clause = set(clause)
            for prop_var, assign_elem in self.assignment.items():
                literal_assigned_false = (
                    -prop_var if assign_elem.truth_val else prop_var
                )
                if literal_assigned_false in tmp_clause:
                    tmp_clause.remove(literal_assigned_false)
            f_a[frozenset(tmp_clause)] = clause

        self.calculate_f_a_time += time.time() - start_time

        return f_a

    def update_f_a(self, f_a, prop_var, truth_val):
        start_time = time.time()

        new_f_a = {}
        true_literal = prop_var if truth_val else -prop_var
        false_literal = -prop_var if truth_val else prop_var
        for clause in f_a.keys():
            if true_literal in clause:
                continue
            tmp_clause = set(clause)
            if false_literal in clause:
                tmp_clause.remove(false_literal)
            new_f_a[frozenset(tmp_clause)] = f_a[clause]

        self.update_f_a_time += time.time() - start_time
        return new_f_a

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

    def print_assignment(self):
        for prop_val, assignment_elem in self.assignment.items():
            print(f"{prop_val}: {assignment_elem}", end=", ")
        print("")


if __name__ == "__main__":
    dpll = DPLL()
    assignment = dpll.dpll()
    if assignment:
        print("s SATISFIABLE")
        assignment_lst = [
            (prop_var if assignment_elem.truth_val else -prop_var)
            for prop_var, assignment_elem in assignment.items()
        ]
        output = (
            "v " + " ".join(str(assignment) for assignment in assignment_lst) + " 0"
        )
        print(output)
    else:
        print("s UNSATISFIABLE")
