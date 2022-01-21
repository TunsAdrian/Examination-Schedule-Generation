import numpy
from z3 import *
import itertools
import numpy as np

# Making constraints
def get_col(arr, col):
    return map(lambda x : x[col], arr)

#times = [8, 10, 12, 14, 16, 18]
times = [12,14]
#days = [10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 24, 25, 26, 27, 28]
days = [29,30,31]
exams = [["DAIR", "BD", "Raluca-Muresan"], ["DAIR2", "BD", "Raluca-Muresan"],  ["DAIR3", "AIDC", "Raluca-Muresan"]]
batchs = ["AIDC", "BD"]

time_slots = {}
j =0;

for i in itertools.product(days, times):
	time_slots[j] = i
	j += 1

print(time_slots.values())

course_times = {}

nr = len(exams)
nr2 = len(time_slots)

j=0

for i in itertools.product(exams, time_slots.values()):
	name = i[0][0] + " " + i[0][1] +" "+i[0][2] +" " +str(i[1][0]) + " " + str(i[1][1])
	#print(name)
	course_times[j] = Bool(name)
	j += 1

all_times = list(course_times.values())
print(all_times[1])
appointments = []
time_slots = list(time_slots.values())

print(time_slots)

for time in all_times:
	time = str(time)
	time = time.split(sep=" ", maxsplit=4)
	appointments.append(time)

print(appointments)



# ---------------------------------------------------------------------------------------
# CONSTRAINTS
# ---------------------------------------------------------------------------------------

#no exams from the same teacher overlapping
aux = []

for i,appointment in enumerate(appointments):
	for j,appointment2 in enumerate(appointments):
		if appointment != appointment2:
			if appointment[0] != appointment2[0]:
				if appointment[2] == appointment2[2]:
					if appointment[3] == appointment2[3]:
						if appointment[4] == appointment2[4]:
							aux.append(Implies(all_times[i], Not(all_times[j])))

							#aux.append(Or(all_times[i], all_times[j]))

exams_from_same_teacher = And(aux);
#all exams should be scheduled and only once
aux = []
aux2 = []
for i,appointment in enumerate(appointments):
	aux.append(all_times[i])
	if((i+1) % len(time_slots) == 0):
		aux2.append(Or(aux))
		aux = []

all_exams_taken = And(aux2)
#only one exam taken by a batch in a day

aux2 = []

# for b in batchs:
# 	aux = []
# 	for d in days:
# 		for i,appointment in enumerate(appointments):
# 			if appointment[1] == b:
# 				if appointment[3] == d:
# 					aux.append(Or(appointment))
#
# 	aux2.append(And(aux))
#
#
# exams_from_same_batch = And(aux2)
for i,appointment in enumerate(appointments):
	for j,appointment2 in enumerate(appointments):
		if appointment != appointment2:
			if appointment[1] == appointment2[1]:
				if appointment[3] == appointment2[3]:
					# print(all_times[i])
					# print(appointment)
					# print('**')
					# print(appointment2)
					# print(all_times[j])
					# print('--------------')
					aux.append(Implies(all_times[i],Not(all_times[j])))
					#aux.append(Or(all_times[i], all_times[j]))

exams_from_same_batch = And(aux)

#if there are more exams taken by a batch, the exam should not be on the same day
aux = []
for i, appointment in enumerate(appointments):
	for j, appointment2 in enumerate(appointments):
		if appointment != appointment2:
			if appointment[1] == appointment2[1]:
				if appointment[0] != appointment2[0]:
					if abs(int(appointment[3]) - int(appointment2[3])) > 1:
						print(abs(int(appointment[3]) - int(appointment2[3])))
						aux.append(Implies(all_times[i], all_times[j]))


exams_days_diff = And(aux)
solver = Solver()


solver.add(all_exams_taken)
#solver.add(exams_from_same_batch)
solver.add(exams_from_same_teacher)
solver.add(exams_days_diff)

print(solver)
if solver.check() == sat:
	print('sat')
	model = solver.model()
	for time in all_times:
		if model.evaluate(time):
			print(time)
	print(model)
else:
	print('unsat')








