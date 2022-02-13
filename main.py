from z3 import *
import csv
import tabulate

# TODO: take from GUI
timePerExam = 2
examsStartingHour = 8
numberOfTimeSlots = 2
numberOfDays = 7
###

coursesWithSpecialization = {}
courseDict = {}
slotDict = {}

with open('Exams-proba.csv', 'r') as file:
    csvReader = csv.reader(file, delimiter=',')
    header = next(csvReader)

    # strip leading/trailing spaces and replace the rest with "-"
    for row in csvReader:
        row[0] = ' '.join(row[0].split()).replace(' ', '-')
        row[1] = ' '.join(row[1].split()).replace(' ', '-')
        row[2] = ' '.join(row[2].split()).replace(' ', '-')
        row[3] = ' '.join(row[3].split()).replace(' ', '-')

        # create exam key with subject name, teacher and year and append the section and year to the list values
        # e.g. key: Subject~Professor~Year, value: SectionYear
        if row[0] + '~' + row[2] + '~' + row[3] in coursesWithSpecialization.keys():
            coursesWithSpecialization[row[0] + '~' + row[2] + '~' + row[3]].append(row[1] + row[3])
        else:
            coursesWithSpecialization[row[0] + '~' + row[2] + '~' + row[3]] = [row[1] + row[3]]

# convert dict to list of lists
coursesWithSpecialization = list(map(list, coursesWithSpecialization.items()))

# compute total number of exam slots
numberOfSlots = numberOfDays * numberOfTimeSlots

# create dict of keys and a single list with specializations
for course in coursesWithSpecialization:
    courseDict[str(course[0])] = {"specializations": [str(specialization) for specialization in course[1]]}

# create dictionary with key subject name, teacher year and values same key with nr of days and nr of time slots
for course in courseDict:
    for specialization in courseDict[course]["specializations"]:
        slotDict[course + '/' + specialization] = [Bool(course + '/' + specialization + '/' + str(j) + '/' + str(i))
                                                   for i in range(numberOfDays)
                                                   for j in range(numberOfTimeSlots)]

solver = Solver()

# At most one exam for each course and each specialization taking that course in the whole timetable
for slotEntry in slotDict:
    for i in range(numberOfSlots):
        for j in range(numberOfSlots):
            if i != j:
                solver.add(Implies(slotDict[slotEntry][i], Not(slotDict[slotEntry][j])))
print("1. Ensured at most one exam per course and each specialization")

# There should be at least one exam for each course and each specialization taking that course for all days
for slotEntry in slotDict:
    solver.add(Or([slots for slots in slotDict[slotEntry]]))
print("2. Ensured at least one exam for each course and specialization")

# For all specializations taking a particular course the exam should be on the same day
for slotEntry in slotDict:
    for i in range(numberOfSlots):
        for remaining in slotDict:
            if remaining.split('/')[0] == slotEntry.split('/')[0] and slotEntry != remaining:
                solver.add(Implies(slotDict[slotEntry][i], slotDict[remaining][i]))
print("3. Ensured all specialization take the exams with same name and teacher on the same day")

# There can only be one exam of a specialization in one day
for slotEntry in slotDict:
    for i in range(numberOfSlots):
        for remaining in slotDict:
            if remaining.split('/')[1] == slotEntry.split('/')[1] and slotEntry != remaining:
                y = int(i / numberOfTimeSlots)
                y = y * numberOfTimeSlots
                for j in range(y, y + numberOfTimeSlots):
                    solver.add(Implies(slotDict[slotEntry][i], Not(slotDict[remaining][j])))
print("4. Ensured a specialization will have at most one exam in a day")

# There can only be one exam of a teacher in one timeslot
for slotEntry in slotDict:
    for i in range(numberOfSlots):
        for remaining in slotDict:
            # check teacher name
            if remaining.split('/')[0].split('~')[1] == slotEntry.split('/')[0].split('~')[1] and slotEntry != remaining:
                y = int(i / numberOfTimeSlots)
                y = y * numberOfTimeSlots
                for j in range(y, y + numberOfTimeSlots):
                    # check if current entry has the same day and hour as the others, and that it doesn't have
                    # the same exam name
                    if slotDict[slotEntry][i].__str__().split('/')[0].split('~')[0] != \
                            slotDict[remaining][j].__str__().split('/')[0].split('~')[0] and \
                            slotDict[slotEntry][i].__str__().split('/')[3] == \
                            slotDict[remaining][j].__str__().split('/')[3] and \
                            slotDict[slotEntry][i].__str__().split('/')[2] == \
                            slotDict[remaining][j].__str__().split('/')[2]:
                        solver.add(Implies(slotDict[slotEntry][i], Not(slotDict[remaining][j])))
print("5. Ensured a teacher can have at most one exam in a timeslot")

# TODO: add constraint for having days between exams and for having options for packets of optionals

final_schedule = []
time_dict = {}

# create a dictionary of timeslot keys and corresponding hour
for i in range(numberOfTimeSlots):
    time_dict[i] = f'{examsStartingHour}:00 - {examsStartingHour + timePerExam}:00'
    examsStartingHour += timePerExam

if solver.check() == sat:

    print('status: sat\n')
    model = solver.model()

    for slotEntry in slotDict:
        for slot in range(numberOfSlots):
            if model.evaluate(slotDict[slotEntry][slot]):
                result = slotDict[slotEntry][slot].__str__().split('/')

                examName = result[0].split('~')[0].replace('-', ' ')
                specialization2 = result[1][0:2].replace('-', ' ')
                year = result[1][-1].replace('-', ' ')
                teacher = result[0].split('~')[1].replace('-', ' ')
                day = str(int(result[3]) + 1)
                hourSlot = int(result[2])

                final_schedule.append([examName, specialization2, year, teacher, day, time_dict[hourSlot]])
else:
    print('status: unsat\n')

if final_schedule:
    # sort final schedule by day, and then by specialization year
    final_schedule.sort(key=lambda x: (x[4], x[2]))
    final_schedule.insert(0, ["Exam-Name", "Specialization", "Year", "Teacher", "Day", "Hour"])
    print(tabulate.tabulate(final_schedule, headers="firstrow"))
else:
    print("---A proper schedule could not be generated for the input data---")
