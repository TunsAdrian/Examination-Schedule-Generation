from z3 import *
import itertools
import csv
import tabulate
import numpy as np

# times = [8, 10, 12, 14, 16, 18]
times = [12, 14]
# days = [10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 24, 25, 26, 27, 28]
days = [30]
time_slots = {}
exams = []
j = 0

# exams = [["DAIR", "AIDC", "Raluca-Muresan"], ["DAIR2", "BD", "Raluca-Muresan"]]
with open('Exams.csv', 'r') as file:
    csvReader = csv.reader(file, delimiter=',')
    header = next(csvReader)
    for row in csvReader:
        row[0] = ' '.join(row[0].split()).replace(' ', '-')
        row[1] = ' '.join(row[1].split()).replace(' ', '-')
        row[2] = ' '.join(row[2].split()).replace(' ', '-')
        row[3] = ' '.join(row[3].split()).replace(' ', '-')

        exams.append(row)


# Making constraints
def get_col(arr, col):
    return map(lambda x: x[col], arr)


for i in itertools.product(days, times):
    time_slots[j] = i
    j += 1

# time_slots = list(time_slots.values())
# print(type(time_slots[1]))
print(time_slots.values())

course_times = {}

nr = len(exams)
nr2 = len(time_slots)

j = 0

for i in itertools.product(exams, time_slots.values()):
    name = i[0][0] + " " + i[0][1] + " " + i[0][2] + " " + str(i[1][0]) + " " + str(i[1][1])
    # print(name)
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

# no exams from the same teacher overlapping
aux = []

for i, appointment in enumerate(appointments):
    for j, appointment2 in enumerate(appointments):
        if appointment != appointment2:
            if appointment[0] != appointment2[0]:
                if appointment[2] == appointment2[2]:
                    if appointment[3] == appointment2[3]:
                        if appointment[4] == appointment2[4]:
                            aux.append(Implies(all_times[i], Not(all_times[j])))

            # aux.append(Or(all_times[i], all_times[j]))

exams_from_same_teacher = And(aux)
# all exams should be scheduled and only once
aux = []
aux2 = []
for i, appointment in enumerate(appointments):
    aux.append(all_times[i])
    if (i + 1) % len(time_slots) == 0:
        aux2.append(Or(aux))
        aux = []

all_exams_taken = And(aux2)
# only one exam taken by a batch in a day

aux = []

for i, appointment in enumerate(appointments):
    for j, appointment2 in enumerate(appointments):
        if appointment != appointment2:
            if appointment[1] == appointment2[1]:
                if appointment[3] == appointment2[3]:
                    # print(all_times[i])
                    # print(appointment)
                    # print('**')
                    # print(appointment2)
                    # print(all_times[j])
                    # print('--------------')
                    aux.append(Implies(all_times[i], Not(all_times[j])))
        # aux.append(Or(all_times[i], all_times[j]))

exams_from_same_batch = And(aux)

# if there are more exams taken by a batch, the exam should be on the same day

solver = Solver()

solver.add(exams_from_same_batch)
solver.add(exams_from_same_teacher)
solver.add(all_exams_taken)

final_schedule = []
print(solver)
if solver.check() == sat:
    print('sat')
    model = solver.model()
    for time in all_times:
        if model.evaluate(time):
            final_schedule.append(time.__str__().split())
# print(model)
else:
    print('unsat')

if final_schedule:
    final_schedule.insert(0, ["Exam-Name", "Specialization", "Teacher", "Day", "Hour"])
    print(tabulate.tabulate(final_schedule, headers="firstrow"))
else:
    print("---A proper schedule could not be generated for the input data---")
