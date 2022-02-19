from z3 import *
import csv
import tabulate

days_number = 10
timeslots_number = 3
time_per_exam = 2
exams_starting_hour = 8

courses_dict = {}
slot_dict = {}


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
    if subject + '~' + teacher + '~' + year in courses_dict.keys():
        courses_dict[subject + '~' + teacher + '~' + year]["specializations"].append(section + year)
    else:
        courses_dict[subject + '~' + teacher + '~' + year] = {"specializations": [section + year]}


with open('Exams.csv', 'r') as file:
    csv_reader = csv.reader(file, delimiter=',')
    next(csv_reader)

    for row in csv_reader:
        validate_input(row)

        # check if subject and teacher fields have '/' (denoting packages of optional subjects) and register each
        # subject-teacher entry
        if row[0].find('/') != -1 and row[2].find('/') != -1:
            optional_subjects = row[0].split('/')
            optional_subjects_teachers = row[2].split('/')

            if len(optional_subjects) != len(optional_subjects_teachers):
                raise Exception(f"{row[0]} doesn't have teachers specified for all subjects.")

            for i in range(len(optional_subjects)):
                create_courses_dict(optional_subjects[i], row[1], optional_subjects_teachers[i], row[3])

        else:
            create_courses_dict(row[0], row[1], row[2], row[3])

# create a dict with key from exam name, teacher, year and values from list of same key with nr of days and of timeslots
for course in courses_dict:
    for specialization in courses_dict[course]["specializations"]:
        # e.g. key: Subject~Professor~Year/SpecializationYear, value: list with: [key + /day/timeslot]
        slot_dict[course + '/' + specialization] = [Bool(course + '/' + specialization + '/' + str(i) + '/' + str(j))
                                                    for i in range(days_number)
                                                    for j in range(timeslots_number)]

# compute total number of exam slots
number_of_slots = days_number * timeslots_number

solver = Solver()

# At most one exam for each course and each specialization taking that course in the whole timetable
for slotEntry in slot_dict:
    for i in range(number_of_slots):
        for j in range(number_of_slots):
            if i != j:
                solver.add(Implies(slot_dict[slotEntry][i], Not(slot_dict[slotEntry][j])))
print("1. Ensured at most one exam for each course and specialization")

# At least one exam for each course and each specialization taking that course for all days
for slotEntry in slot_dict:
    solver.add(Or([slots for slots in slot_dict[slotEntry]]))
print("2. Ensured at least one exam for each course and specialization")

# For all specializations having a specific exam with the same teacher, the exam should be on the same day
for slotEntry in slot_dict:
    for i in range(number_of_slots):
        for remaining in slot_dict:
            if remaining.split('/')[0] == slotEntry.split('/')[0] and slotEntry != remaining:
                solver.add(Implies(slot_dict[slotEntry][i], slot_dict[remaining][i]))
print("3. Ensured all specialization take the exams with same exam name and teacher on the same day")

# At most one exam for a specialization in one day
for slotEntry in slot_dict:
    for i in range(number_of_slots):
        for remaining in slot_dict:
            # check specialization name
            if remaining.split('/')[1] == slotEntry.split('/')[1] and slotEntry != remaining:
                y = int(i / timeslots_number)
                y = y * timeslots_number

                for j in range(y, y + timeslots_number):
                    solver.add(Implies(slot_dict[slotEntry][i], Not(slot_dict[remaining][j])))
print("4. Ensured a specialization will have at most one exam in a day")

# At most one exam for a teacher in one timeslot
for slotEntry in slot_dict:
    for i in range(number_of_slots):
        for remaining in slot_dict:
            # check teacher name
            if remaining.split('/')[0].split('~')[1] == slotEntry.split('/')[0].split('~')[1] and slotEntry != remaining:
                y = int(i / timeslots_number)
                y = y * timeslots_number

                for j in range(y, y + timeslots_number):
                    # check if current entry has the same day and hour as the others, and that it doesn't have
                    # the same exam name
                    if slot_dict[slotEntry][i].__str__().split('/')[0].split('~')[0] != \
                            slot_dict[remaining][j].__str__().split('/')[0].split('~')[0] and \
                            slot_dict[slotEntry][i].__str__().split('/')[2] == \
                            slot_dict[remaining][j].__str__().split('/')[2] and \
                            slot_dict[slotEntry][i].__str__().split('/')[3] == \
                            slot_dict[remaining][j].__str__().split('/')[3]:
                        solver.add(Implies(slot_dict[slotEntry][i], Not(slot_dict[remaining][j])))
print("5. Ensured a teacher can have at most one exam in a timeslot")

final_schedule = []
time_dict = {}

# create a dictionary of timeslot keys and corresponding hours
for i in range(timeslots_number):
    time_dict[i] = f'{(exams_starting_hour % 24):02d}:00 - {((exams_starting_hour + time_per_exam) % 24):02d}:00'
    exams_starting_hour += time_per_exam

if solver.check() == sat:
    print('status: sat\n')
    model = solver.model()

    for slotEntry in slot_dict:
        for slot in range(number_of_slots):
            if model.evaluate(slot_dict[slotEntry][slot]):
                result_list = slot_dict[slotEntry][slot].__str__().split('/')
                key_list = result_list[0].split('~')

                hour_slot = int(result_list[3])
                exam_day = str(int(result_list[2]) + 1)
                teacher_name = key_list[1].replace('-', ' ')
                specialization_year = key_list[2]
                specialization_name = result_list[1].replace(specialization_year, '')
                exam_name = key_list[0].replace('-', ' ')

                final_schedule.append([exam_name, specialization_name, specialization_year, teacher_name,
                                       exam_day, time_dict[hour_slot]])
else:
    print('status: unsat\n')

if final_schedule:
    # sort final schedule by day, and then by specialization year
    final_schedule.sort(key=lambda x: (int(x[4]), int(x[2])))
    final_schedule.insert(0, ["Exam-Name", "Specialization", "Year", "Teacher", "Day", "Hour"])

    print(tabulate.tabulate(final_schedule, headers="firstrow", tablefmt="fancy_grid"))
else:
    print("---A proper schedule could not be generated for the input data---")
