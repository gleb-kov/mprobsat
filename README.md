# Merging variables based probSAT solver
probSAT algorithm + merging variable algorithm

https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.190/Mitarbeiter/balint/SAT2012.pdf

# Benchmarks

Solver           | md5-0 | md5-5 | md5-10 | md5-20 | sha2-0 | sha2-5 | sha2-10 | sha2-20 |
---------------- | - | - | - | - | - | - | - | - |
probsat-poly     | - | - | - | - | - | - | - | - |
probsat-exp      | - | - | - | - | - | - | - | - |
probsat-poly-nc  | - | - | - | - | - | - | - | - |
probsat-exp-nc   | - | - | - | - | - | - | - | - |
mprobsat-poly    | - | - | - | - | - | - | - | - |
mprobsat-exp     | - | - | - | - | - | - | - | - |
mprobsat-poly-nc | - | - | - | - | - | - | - | - |
mprobsat-exp-nc  | - | - | - | - | - | - | - | - |

# Acknowledgments probSAT

- в оригинальном probSat солвер cb заточен только для poly случая

# mprobSAT TODO's
- подобрать cb для mprobsat
- попробовать формулу с make для mprobsat
- заточить гиперпараметры mprobsat
