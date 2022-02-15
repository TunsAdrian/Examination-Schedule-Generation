from z3 import *
import csv
import tabulate

# TODO: take from GUI
timePerExam = 2
examsStartingHour = 8
timeslotsNumber = 3
daysNumber = 10
###

coursesDict = {}
slotDict = {}


def validate_input(row_data):
    if ' '.join(row_data).find('~') != -1:
        raise Exception("Input data can't contain the following characters: '~'")
    if row_data[1].find('/') != -1 or row_data[3].find('/') != -1:
        raise Exception("Section and Year can't contain the following characters: '/'")


def create_courses_dict(subject, section, teacher, year):
    # strip leading/trailing spaces and replace the rest with "-"
    subject = ' '.join(subject.split()).replace(' ', '-')
    section = ' '.join(section.split()).replace(' ', '-')
    teacher = ' '.join(teacher.split()).replace(' ', '-')
    year = ' '.join(year.split()).replace(' ', '-')

    # create a dict with key made from exam subject name, teacher and year and value from a list containing the
    # section and year
    # e.g. key: Subject~Professor~Year, value: [Specialization1Year, Specialization2Year]
    if subject + '~' + teacher + '~' + year in coursesDict.keys():
        coursesDict[subject + '~' + teacher + '~' + year]["specializations"].append(section + year)
    else:
        coursesDict[subject + '~' + teacher + '~' + year] = {"specializations": [section + year]}


with open('Exams.csv', 'r') as file:
    csvReader = csv.reader(file, delimiter=',')
    header = next(csvReader)

    for row in csvReader:
        validate_input(row)

        # check if subject and teacher fields have '/' (denoting packages of optional subjects) and register each
        # subject-teacher entry
        if row[0].find('/') != -1 and row[2].find('/') != -1:
            optionalSubjects = row[0].split('/')
            optionalSubjectsTeachers = row[2].split('/')

            if len(optionalSubjects) != len(optionalSubjectsTeachers):
                raise Exception(f"{row[0]} doesn't have teachers specified for all subjects.")

            for i in range(len(optionalSubjects)):
                create_courses_dict(optionalSubjects[i], row[1], optionalSubjectsTeachers[i], row[3])

        else:
            create_courses_dict(row[0], row[1], row[2], row[3])

# create a dict with key from exam name, teacher, year and values from list of same key with nr of days and of timeslots
for course in coursesDict:
    for specialization in coursesDict[course]["specializations"]:
        # e.g. key: Subject~Professor~Year/SpecializationYear, value: list with: [key + /day/timeslot]
        slotDict[course + '/' + specialization] = [Bool(course + '/' + specialization + '/' + str(i) + '/' + str(j))
                                                   for i in range(daysNumber)
                                                   for j in range(timeslotsNumber)]

# compute total number of exam slots
numberOfSlots = daysNumber * timeslotsNumber

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
                y = int(i / timeslotsNumber)
                y = y * timeslotsNumber

                for j in range(y, y + timeslotsNumber):
                    solver.add(Implies(slotDict[slotEntry][i], Not(slotDict[remaining][j])))
print("4. Ensured a specialization will have at most one exam in a day")

# At most one exam for a teacher in one timeslot
for slotEntry in slotDict:
    for i in range(numberOfSlots):
        for remaining in slotDict:
            # check teacher name
            if remaining.split('/')[0].split('~')[1] == slotEntry.split('/')[0].split('~')[1] and slotEntry != remaining:
                y = int(i / timeslotsNumber)
                y = y * timeslotsNumber

                for j in range(y, y + timeslotsNumber):
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

# TODO: add constraint for having days between exams

finalSchedule = []
timeDict = {}

# create a dictionary of timeslot keys and corresponding hours
for i in range(timeslotsNumber):
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
    finalSchedule.sort(key=lambda x: (int(x[4]), int(x[2])))
    finalSchedule.insert(0, ["Exam-Name", "Specialization", "Year", "Teacher", "Day", "Hour"])
    print(tabulate.tabulate(finalSchedule, headers="firstrow", tablefmt="fancy_grid"))
else:
    print("---A proper schedule could not be generated for the input data---")

# TODO: use in GUI for generating file with schedule
# with open('exams-schedule.txt', 'w') as file:
#     file.write(tabulate.tabulate(finalSchedule))
