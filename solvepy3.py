import copy
import random
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
            elif match_pcnf := re.search(r"^p\s+cnf\s+(\d+)\s+(\d+)", line):
                num_vars = int(match_pcnf.group(1))
                num_clauses = int(match_pcnf.group(2))
            else:
                literal_lst = [int(x) for x in re.findall(r"-?\d+", line)]
                acc_literal_lst = acc_literal_lst + literal_lst
                if 0 in acc_literal_lst:
                    acc_literal_lst.remove(0)
                    cnf_formula.add(frozenset(acc_literal_lst))
                    acc_literal_lst = []

        # input informations
        self.num_vars, self.num_clauses = num_vars, num_clauses
        # store cnf_formula
        self.cnf_formula = cnf_formula
        # store original cnf_formula
        self.original_cnf_formula = copy.deepcopy(cnf_formula)

        # prop_var|-> assignment_elem
        self.assignment = {}
        # f_a
        self.f_a = self.init_f_a()
        # literal|-> set of clauses that contains literal
        self.literal_map = self.init_literal_map()
        # store current unit clauses
        self.unit_clauses = self.init_unit_clauses()
        # store current conflict clause
        self.conflict_clause = None
        # count number of conflicts
        self.conflict_cnt = 0

    # init util functions
    def init_f_a(self):
        f_a = {}
        for clause in self.cnf_formula:
            f_a[clause] = set(clause)
        return f_a

    def init_literal_map(self):
        literal_map = {}
        for i in range(1, self.num_vars + 1):
            literal_map[i] = set()
            literal_map[-i] = set()
        for clause in self.cnf_formula:
            for literal in clause:
                literal_map[literal].add(clause)
        return literal_map

    def init_unit_clauses(self):
        unit_clauses = set()
        for clause in self.cnf_formula:
            if len(clause) == 1:
                unit_clauses.add(clause)
        return unit_clauses

    # dpll algorithm
    def dpll(self):
        while True:
            self.unit_prop()
            if self.satisfied():
                return self.assignment
            elif conflict_clause := self.take_conflict_clause():
                clause = self.learn(conflict_clause)
                if len(clause) == 0:
                    return None
                self.add_clause(clause)
                self.conflict_cnt = self.conflict_cnt + 1
                if self.conflict_cnt % 700 == 0:
                    while len(self.assignment) > 0:
                        self.pop_assignment()
                else:
                    while not self.is_unit_clause(clause):
                        self.pop_assignment()
            else:
                x = max(
                    range(1, self.num_vars + 1),
                    key=lambda x: 0
                    if x in self.assignment.keys()
                    else max(len(self.literal_map[x]), len(self.literal_map[-x])),
                )
                if len(self.literal_map[x]) > len(self.literal_map[-x]):
                    self.add_assignment(x, self.AssignmentElem(True, None))
                else:
                    self.add_assignment(x, self.AssignmentElem(False, None))
                # for i in range(1, self.num_vars + 1):
                #     if i in self.assignment.keys():
                #         continue
                #     self.add_assignment(i, self.AssignmentElem(False, None))
                #     break

    # unit propagation
    def unit_prop(self):
        while res := self.find_literal_in_unit_clause():
            prop_var, truth_val, imply_clause = res
            self.add_assignment(prop_var, self.AssignmentElem(truth_val, imply_clause))

    # find unit literal info: prop_var, truth_val, imply_clause that makes literal true
    def find_literal_in_unit_clause(self):
        if len(self.unit_clauses) > 0:
            unit_clause = self.unit_clauses.pop()
            unit_clause_f_a = self.f_a[unit_clause]
            literal = set(unit_clause_f_a).pop()
            return abs(literal), (True if literal > 0 else False), unit_clause
        else:
            return None

    # check if cnf formula satisfied
    def satisfied(self):
        for full_clause, f_a_clause in self.f_a.items():
            # if some of clause is not true clause, return false
            if f_a_clause is not None:
                return False
        return True

    # take conflict clause and set it as None
    def take_conflict_clause(self):
        if self.conflict_clause is not None:
            conflict_clause = self.conflict_clause
            self.conflict_clause = None
            return conflict_clause
        else:
            return None

    # update cnf_formula, literal_map, f_a, unit_clauses
    def add_clause(self, clause):
        # update cnf_formula
        self.cnf_formula.add(clause)

        # update literal_map
        for literal in clause:
            self.literal_map[literal].add(clause)

        # update f_a, unit_clauses
        f_a_clause = set(clause)
        for literal in clause:
            prop_var = abs(literal)
            if not (prop_var in self.assignment):
                continue
            truth_val = self.assignment[prop_var].truth_val
            if literal > 0 and truth_val == True:
                f_a_clause = None
                break
            elif literal > 0 and truth_val == False:
                f_a_clause.remove(literal)
            elif literal < 0 and truth_val == True:
                f_a_clause.remove(literal)
            elif literal < 0 and truth_val == False:
                f_a_clause = None
                break
        self.f_a[clause] = f_a_clause
        if f_a_clause is not None:
            if len(f_a_clause) == 0:
                self.conflict_clause = clause
            elif len(f_a_clause) == 1:
                self.unit_clauses.add(clause)

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
            if self.assignment[pi].imply_clause is not None and (pi in D or -pi in D):
                D = self.resolve(self.assignment[pi].imply_clause, D, pi)

        return D

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

    def is_unit_clause(self, clause):
        if self.f_a[clause] is not None and len(self.f_a[clause]) == 1:
            return True
        else:
            return False

    # add assignment(then update f_a, unit_clauses, conflict_clause)
    def add_assignment(self, prop_var, assignment_elem):
        self.assignment[prop_var] = assignment_elem
        true_literal = prop_var if assignment_elem.truth_val else -prop_var
        false_literal = -true_literal
        modify_clauses = (
            self.literal_map[prop_var] if prop_var in self.literal_map else set()
        ) | (self.literal_map[-prop_var] if -prop_var in self.literal_map else set())

        # adding assignment for prop_var may affect unit_clauses
        self.unit_clauses = self.unit_clauses - modify_clauses

        # update f_a, unit_clauses, conflict_clause
        for clause in modify_clauses:
            # if clause is already true clause
            if self.f_a[clause] is None:
                continue
            elif false_literal in clause:
                self.f_a[clause].remove(false_literal)
                if len(self.f_a[clause]) == 0:
                    self.conflict_clause = clause
                elif len(self.f_a[clause]) == 1:
                    self.unit_clauses.add(clause)
            elif true_literal in clause:
                # contain true literal -> entire clause is true
                self.f_a[clause] = None

        # update conflict clause
        if self.conflict_clause is not None:
            if len(self.f_a[self.conflict_clause]) > 0:
                self.conflict_clause = None

    # pop assignment(then update f_a, unit_clauses, conflict_clause)
    def pop_assignment(self):
        prop_var, assignment_elem = self.assignment.popitem()
        true_literal = prop_var if assignment_elem.truth_val else -prop_var
        false_literal = -true_literal
        modify_clauses = (
            self.literal_map[prop_var] if prop_var in self.literal_map else set()
        ) | (self.literal_map[-prop_var] if -prop_var in self.literal_map else set())
        # popping assignment for prop_var may affect unit_clauses
        self.unit_clauses = self.unit_clauses - modify_clauses

        # update f_a, unit_clauses, conflict_clause
        for clause in modify_clauses:
            if true_literal in clause:
                f_a_clause = set(clause)
                for literal in clause:
                    prop_var = abs(literal)
                    if not (prop_var in self.assignment):
                        continue
                    truth_val = self.assignment[prop_var].truth_val
                    if literal > 0 and truth_val == True:
                        f_a_clause = None
                        break
                    elif literal > 0 and truth_val == False:
                        f_a_clause.remove(literal)
                    elif literal < 0 and truth_val == True:
                        f_a_clause.remove(literal)
                    elif literal < 0 and truth_val == False:
                        f_a_clause = None
                        break
                self.f_a[clause] = f_a_clause
                if f_a_clause is not None:
                    if len(f_a_clause) == 0:
                        self.conflict_clause = clause
                    elif len(f_a_clause) == 1:
                        self.unit_clauses.add(clause)
            elif false_literal in clause and self.f_a[clause] is not None:
                self.f_a[clause].add(false_literal)
                if len(self.f_a[clause]) == 1:
                    self.unit_clauses.add(clause)

        # update conflict clause
        if self.conflict_clause is not None:
            if len(self.f_a[self.conflict_clause]) > 0:
                self.conflict_clause = None

    # for debugging
    def check(self, assignment_lst):
        true_literal = []
        false_literal = []
        for a in assignment_lst:
            true_literal.append(a)
            false_literal.append(-a)

        cnf_formula = copy.deepcopy(self.original_cnf_formula)
        res_cnf_formula = set()
        for clause in cnf_formula:
            is_true = False
            tmp_clause = set(clause)
            for literal in clause:
                if literal in true_literal:
                    is_true = True
                    break
                if literal in false_literal:
                    tmp_clause.remove(literal)
            if is_true:
                continue
            else:
                res_cnf_formula.add(frozenset(tmp_clause))

        if len(res_cnf_formula) == 0:
            return True
        if frozenset() in res_cnf_formula:
            return False


if __name__ == "__main__":
    start_time = time.time()
    dpll = DPLL()
    res = dpll.dpll()
    if res:
        print("s SATISFIABLE")
        assignment_lst = [
            (prop_var if assignment_elem.truth_val else -prop_var)
            for prop_var, assignment_elem in res.items()
        ]
        output = (
            "v " + " ".join(str(assignment) for assignment in assignment_lst) + " 0"
        )
        print(output)

        print("CHECK!: {}", dpll.check(assignment_lst))
    else:
        print("s UNSATISFIABLE")

    print("elapsed: ", time.time() - start_time)
