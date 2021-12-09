import sys

cnf_formula = sys.argv[1]

result_values = set()
with open("result.txt", 'r') as f:
    for a in f:
        if a == '':
            break
        v = int(a)
        result_values.add(v)

idx = 0
failed_cnt = 0

with open(cnf_formula, 'r') as f:
    for a in f:
        if idx == 0:
            idx = 1
            continue
        l = a.split()
        sat = False
        for elem in l:
            if int(elem) in result_values:
                sat = True
        if sat is False:
            failed_cnt += 1
            print(l)
        idx += 1

print(failed_cnt)
