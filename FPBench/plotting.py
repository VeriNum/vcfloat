import numpy as np
import matplotlib.pyplot as plt


class fpbench_ex:
    "a class for fpbench examples"

    def __init__(self, name) :
        self.name = name
        self.time = 0
        self.ops  = 0
        self.vars = 0
        self.err  = 0.0
        self.fpt  = 0.0
        self.pca  = 0.0
        self.gpa  = 0.0
        self.type = ""


carbonGas = fpbench_ex("carbonGas")
carbonGas.time = 6.18
carbonGas.ops  = 11
carbonGas.vars = 1
carbonGas.err  = 2.50E-08
carbonGas.type = "proper_rational"
carbonGas.fpt = 9.20E-09
carbonGas.name = "carbonGas"



doppler1 = fpbench_ex("doppler1")
doppler1.time = 72.03
doppler1.ops  = 8
doppler1.vars = 3
doppler1.err  = 4.50E-13
doppler1.type = "proper_rational"
doppler1.fpt  = 1.60E-13

doppler2 = fpbench_ex("doppler2")
doppler2.time = 63.00
doppler2.ops  = 8
doppler2.vars = 3
doppler2.err  = 1.19E-12
doppler2.type = "proper_rational"
doppler2.fpt  = 2.90E-13

doppler3 = fpbench_ex("doppler3")
doppler3.time = 38.41
doppler3.ops  = 8
doppler3.vars = 3
doppler3.err  = 1.72E-13
doppler3.type = "proper_rational"
doppler3.fpt  = 8.30E-14

himmilbeau = fpbench_ex("himmilbeau")
himmilbeau.time = 3.62
himmilbeau.ops  = 14
himmilbeau.vars = 2
himmilbeau.err  = 2.30E-12
himmilbeau.type = "polynomial"
himmilbeau.fpt  = 1.40E-12

jetEngine = fpbench_ex("jetEngine")
jetEngine.time = 120.11
jetEngine.ops  = 48
jetEngine.vars = 2
jetEngine.err  = 1.38E+02
jetEngine.type = "proper_rational"
jetEngine.fpt  = 1.40E-11

nonlin1 = fpbench_ex("nonlin1")
nonlin1.time = 6.18
nonlin1.ops  = 2
nonlin1.vars = 1
nonlin1.err  = 4.39E-16
nonlin1.type = "proper_rational"
nonlin1.fpt  = 5.80E-14

kepler0 = fpbench_ex("kepler0")
kepler0.time = 4.24
kepler0.ops  = 15
kepler0.vars = 6
kepler0.err  = 2.20E-13
kepler0.type = "polynomial"
kepler0.fpt  = 9.50E-14

kepler1 = fpbench_ex("kepler1")
kepler1.time = 11.97
kepler1.ops  = 24
kepler1.vars = 4
kepler1.err  = 1.64E-12
kepler1.type = "polynomial"
kepler1.fpt = 3.60E-13

kepler2 = fpbench_ex("kepler2")
kepler2.time = 28.71
kepler2.ops  = 36
kepler2.vars = 6
kepler2.err  = 6.17E-12
kepler2.type = "polynomial"
kepler2.fpt = 2.00E-12

predprey = fpbench_ex("predprey")
predprey.time = 14.527
predprey.ops  = 7
predprey.vars = 1
predprey.err  = 2.90E-16
predprey.type = "polynomial"
predprey.fpt  = 1.90E-16

rigidBody1 = fpbench_ex("rigidBody1")
rigidBody1.time = 1.589
rigidBody1.ops  = 7
rigidBody1.vars = 3
rigidBody1.err  = 3.05E-13
rigidBody1.type = "polynomial"
rigidBody1.fpt  = 3.90E-13

rigidBody2 = fpbench_ex("rigidBody2")
rigidBody2.time = 4.034
rigidBody2.ops  = 14
rigidBody2.vars = 3
rigidBody2.err  = 3.90E-11
rigidBody2.type = "polynomial"
rigidBody2.fpt = 5.30E-11

verhulst = fpbench_ex("verhulst")
verhulst.time = 7.641
verhulst.ops  = 4
verhulst.vars = 1
verhulst.err  = 2.32E-16
verhulst.type = "polynomial"
verhulst.fpt = 3.30E-16

turbine1 = fpbench_ex("turbine1")
turbine1.time = 48.413
turbine1.ops = 14
turbine1.vars  = 3
turbine1.err  = 7.9e-14
turbine1.type = "proper_rational"
turbine1.fpt  = 2.40E-14

turbine2 = fpbench_ex("turbine2")
turbine2.time = 23.349
turbine2.ops  = 10
turbine2.vars = 3
turbine2.err  = 1.2e-13
turbine2.type = "proper_rational"
turbine2.fpt  = 2.60E-14

turbine3 = fpbench_ex("turbine3")
turbine3.time = 26.161
turbine3.ops  = 14
turbine3.vars = 3
turbine3.err  = 6.1e-14
turbine3.type = "proper_rational"
turbine3.fpt  = 1.30E-14

problem_list = [carbonGas,doppler1,doppler2,doppler3,
himmilbeau,jetEngine,nonlin1,kepler0,kepler1,
kepler2,predprey,rigidBody1,rigidBody2,verhulst,
turbine1,turbine2,turbine3]

problem_list2  = problem_list.copy()
problem_list2.remove(jetEngine)

errors     = [p.err for p in problem_list2]
times      = [p.time for p in problem_list2]
fpt_errors = [p.fpt for p in problem_list2]
err_ratio  = [p.err/p.fpt for p in problem_list2]
ops        = [p.ops for p in problem_list2]


color  = lambda x : 'purple' if x == "proper_rational" else 'green'
area   = lambda x :  (5* x) ** 2

areas  = [ area(p.vars)   for p in problem_list2]
colors = [ color(p.type) for p in problem_list2]

fig, ax = plt.subplots(figsize = (9, 6))
ax.scatter(ops, err_ratio, s=areas, c=colors, edgecolors= "black")
#ax.set_yscale('log')

xy = [(p.err/p.fpt,p.ops) for p in problem_list]

label_dict = {}
i = 0
for c in xy:
    label_dict[problem_list[i].name]=c
    i += 1

label_dict2 = {}
label_dict2["turbine1-3"]=label_dict["turbine1"]
label_dict2["verhulst"]  =label_dict["verhulst"]
label_dict2["rigidBody1, predprey"]  =label_dict["rigidBody1"]
label_dict2["nonlin1"] = label_dict["nonlin1"]
label_dict2["doppler1-3"] = label_dict["doppler1"]
label_dict2["carbonGas"] = label_dict["carbonGas"]


#label_list = label_dict2.keys()

#i=0
#for p in label_list:
    #plt.annotate(p,label_dict2[p])
    #i += 1
plt.show()
