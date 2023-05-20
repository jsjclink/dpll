for i in range(1, 100 + 1):
    num = "0" + str(i)
    filename = "examples/UF150.645.100/uf150-" + num + ".cnf"
    with open(filename, "r+") as f:
        lines = f.readlines()
        f.seek(0)
        f.truncate()
        f.write("".join(lines[:-3]))
