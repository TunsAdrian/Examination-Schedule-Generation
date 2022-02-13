from z3 import *
import csv
import tabulate

# TODO: take from GUI
timePerExam = 2
examsStartingHour = 8
numberOfTimeSlots = 2
numberOfDays = 7
###

coursesDict = {}
slotDict = {}


def validate_input(input_data):
    if input_data.find('/') != -1 or input_data.find('~') != -1:
        raise Exception("Input data can't contain the following characters: '/' '~'")


# TODO: replace with file containing all exams
with open('Exams-proba.csv', 'r') as file:
    csvReader = csv.reader(file, delimiter=',')
    header = next(csvReader)

    # strip leading/trailing spaces and replace the rest with "-"
    for row in csvReader:
        validate_input(' '.join(row))
        row[0] = ' '.join(row[0].split()).replace(' ', '-')
        row[1] = ' '.join(row[1].split()).replace(' ', '-')
        row[2] = ' '.join(row[2].split()).replace(' ', '-')
        row[3] = ' '.join(row[3].split()).replace(' ', '-')

        # create a dict with key made from exam subject name, teacher and year and value from a list containing the
        # section and year
        # e.g. key: Subject~Professor~Year, value: [Specialization1Year, Specialization2Year]
        if row[0] + '~' + row[2] + '~' + row[3] in coursesDict.keys():
            coursesDict[row[0] + '~' + row[2] + '~' + row[3]]["specializations"].append(row[1] + row[3])
        else:
            coursesDict[row[0] + '~' + row[2] + '~' + row[3]] = {"specializations": [row[1] + row[3]]}

# create a dict with key from exam name, teacher, year and values from list of same key with nr of days and of timeslots
for course in coursesDict:
    for specialization in coursesDict[course]["specializations"]:
        # e.g. key: Subject~Professor~Year/SpecializationYear, value: list with: [key + /day/timeslot]
        slotDict[course + '/' + specialization] = [Bool(course + '/' + specialization + '/' + str(i) + '/' + str(j))
                                                   for i in range(numberOfDays)
                                                   for j in range(numberOfTimeSlots)]

# compute total number of exam slots
numberOfSlots = numberOfDays * numberOfTimeSlots

solver = Solver()

# At most one exam for each course and each specialization taking that course in the whole timetable
for slotEntry in slotDict:
    for i in range(numberOfSlots):
        for j in range(numberOfSlots):
            if i != j:
                solver.add(Implies(slotDict[slotEntry][i], Not(slotDict[slotEntry][j])))
print("1. Ensured at most one exam for each course and specialization")

# At least one exam for each course and each specialization taking that course for all days
for slotEntry in slotDict:
    solver.add(Or([slots for slots in slotDict[slotEntry]]))
print("2. Ensured at least one exam for each course and specialization")

# For all specializations having a specific exam with the same teacher, the exam should be on the same day
for slotEntry in slotDict:
    for i in range(numberOfSlots):
        for remaining in slotDict:
            if remaining.split('/')[0] == slotEntry.split('/')[0] and slotEntry != remaining:
                solver.add(Implies(slotDict[slotEntry][i], slotDict[remaining][i]))
print("3. Ensured all specialization take the exams with same exam name and teacher on the same day")

# At most one exam for a specialization in one day
for slotEntry in slotDict:
    for i in range(numberOfSlots):
        for remaining in slotDict:
            # check specialization name
            if remaining.split('/')[1] == slotEntry.split('/')[1] and slotEntry != remaining:
                y = int(i / numberOfTimeSlots)
                y = y * numberOfTimeSlots

                for j in range(y, y + numberOfTimeSlots):
                    solver.add(Implies(slotDict[slotEntry][i], Not(slotDict[remaining][j])))
print("4. Ensured a specialization will have at most one exam in a day")

# At most one exam for a teacher in one timeslot
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
                            slotDict[slotEntry][i].__str__().split('/')[2] == \
                            slotDict[remaining][j].__str__().split('/')[2] and \
                            slotDict[slotEntry][i].__str__().split('/')[3] == \
                            slotDict[remaining][j].__str__().split('/')[3]:
                        solver.add(Implies(slotDict[slotEntry][i], Not(slotDict[remaining][j])))
print("5. Ensured a teacher can have at most one exam in a timeslot")

# TODO: add constraint for having days between exams and for having options for packets of optionals

finalSchedule = []
timeDict = {}

# create a dictionary of timeslot keys and corresponding hours
for i in range(numberOfTimeSlots):
    timeDict[i] = f'{(examsStartingHour % 24):02d}:00 - {((examsStartingHour + timePerExam) % 24):02d}:00'
    examsStartingHour += timePerExam

if solver.check() == sat:
    print('status: sat\n')
    model = solver.model()

    for slotEntry in slotDict:
        for slot in range(numberOfSlots):
            if model.evaluate(slotDict[slotEntry][slot]):
                resultList = slotDict[slotEntry][slot].__str__().split('/')
                keyList = resultList[0].split('~')

                hourSlot = int(resultList[3])
                examDay = str(int(resultList[2]) + 1)
                teacherName = keyList[1].replace('-', ' ')
                specializationYear = keyList[2]
                specializationName = resultList[1].replace(specializationYear, '')
                examName = keyList[0].replace('-', ' ')

                finalSchedule.append([examName, specializationName, specializationYear, teacherName,
                                      examDay, timeDict[hourSlot]])
else:
    print('status: unsat\n')

if finalSchedule:
    # sort final schedule by day, and then by specialization year
    finalSchedule.sort(key=lambda x: (x[4], x[2]))
    finalSchedule.insert(0, ["Exam-Name", "Specialization", "Year", "Teacher", "Day", "Hour"])
    print(tabulate.tabulate(finalSchedule, headers="firstrow", tablefmt="fancy_grid"))
else:
    print("---A proper schedule could not be generated for the input data---")

# TODO: use in GUI for generating file with schedule
# with open('exams-schedule.txt', 'w') as file:
#     file.write(tabulate.tabulate(finalSchedule))
