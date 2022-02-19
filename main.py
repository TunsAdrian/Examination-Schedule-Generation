from z3 import *
import csv
import tabulate
from tkinter import *
from tkinter import filedialog
from tkinter.scrolledtext import ScrolledText


def generate_examination_schedule(days_number, timeslots_number, time_per_exam, exams_starting_hour, file_path):
    # clear result area
    resultArea.delete('1.0', END)

    try:
        days_number = int(days_number.get())
        timeslots_number = int(timeslots_number.get())
        time_per_exam = int(time_per_exam.get())
        exams_starting_hour = int(exams_starting_hour.get())
    except ValueError:
        resultArea.insert(END, "All input values must be completed with whole numbers")
        return

    courses_dict = {}
    slot_dict = {}

    def validate_input(row_data):
        if ' '.join(row_data).find('~') != -1:
            resultArea.insert(END, "Input data can't contain the following characters: '~'")
            raise Exception("Input data can't contain the following characters: '~'")
        if row_data[1].find('/') != -1 or row_data[3].find('/') != -1:
            resultArea.insert(END, "Section and Year can't contain the following characters: '/'")
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

    try:
        with open(file_path, 'r') as file:
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
    except FileNotFoundError:
        resultArea.insert(END, "The .csv file containing the exams could not be found")
        return
    except IOError:
        resultArea.insert(END, "The file could not be read")
        return

    # create a dict with key from exam name, teacher, year and values from list of same key with nr of days and of timeslots
    for course in courses_dict:
        for specialization in courses_dict[course]["specializations"]:
            # e.g. key: Subject~Professor~Year/SpecializationYear, value: list with: [key + /day/timeslot]
            slot_dict[course + '/' + specialization] = [
                Bool(course + '/' + specialization + '/' + str(i) + '/' + str(j))
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
    resultArea.insert(END, "1. Ensured at most one exam for each course and specialization\n")
    resultArea.update()

    # At least one exam for each course and each specialization taking that course for all days
    for slotEntry in slot_dict:
        solver.add(Or([slots for slots in slot_dict[slotEntry]]))
    print("2. Ensured at least one exam for each course and specialization")
    resultArea.insert(END, "2. Ensured at least one exam for each course and specialization\n")
    resultArea.update()

    # For all specializations having a specific exam with the same teacher, the exam should be on the same day
    for slotEntry in slot_dict:
        for i in range(number_of_slots):
            for remaining in slot_dict:
                if remaining.split('/')[0] == slotEntry.split('/')[0] and slotEntry != remaining:
                    solver.add(Implies(slot_dict[slotEntry][i], slot_dict[remaining][i]))
    print("3. Ensured all specialization take the exams with same exam name and teacher on the same day")
    resultArea.insert(END, "3. Ensured all specialization take the exams with same exam name and teacher on the same day\n")
    resultArea.update()

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
    resultArea.insert(END, "4. Ensured a specialization will have at most one exam in a day\n")
    resultArea.update()

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
    resultArea.insert(END, "5. Ensured a teacher can have at most one exam in a timeslot\n")
    resultArea.update()

    final_schedule = []
    time_dict = {}

    # create a dictionary of timeslot keys and corresponding hours
    for i in range(timeslots_number):
        time_dict[i] = f'{(exams_starting_hour % 24):02d}:00 - {((exams_starting_hour + time_per_exam) % 24):02d}:00'
        exams_starting_hour += time_per_exam

    if solver.check() == sat:
        print('status: sat\n')
        resultArea.insert(END, "status: sat\n")
        resultArea.update()

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
        resultArea.insert(END, "status: unsat\n\n")
        resultArea.update()

    if final_schedule:
        # sort final schedule by day, and then by specialization year
        final_schedule.sort(key=lambda x: (int(x[4]), int(x[2])))
        final_schedule.insert(0, ["Exam-Name", "Specialization", "Year", "Teacher", "Day", "Hour"])

        resultArea.after(500, resultArea.delete('1.0', END))
        resultArea.insert(END, tabulate.tabulate(final_schedule, headers="firstrow", tablefmt="fancy_grid"))
        print(tabulate.tabulate(final_schedule, headers="firstrow", tablefmt="fancy_grid"))
    else:
        resultArea.insert(END, "---A proper schedule could not be generated for the input data---")
        print("---A proper schedule could not be generated for the input data---")

    # add space for consecutive application runs (in terminal)
    print("\n\n")


def browse(file_path):
    filename = filedialog.askopenfilename(title="Select a File",
                                          filetypes=(("CSV files", "*.csv*"), ("all files", "*.*")))
    file_path.set(filename)


def save_schedule():
    file_path = filedialog.asksaveasfilename(defaultextension='.txt',
                                             filetypes=(("Text files", "*.txt"), ("all files", "*.*")))
    if file_path is None:
        return

    try:
        with open(file_path, 'w', encoding='UTF-8') as file:
            schedule_result = resultArea.get(1.0, END)
            file.write(schedule_result)
    except IOError:
        resultArea.insert(0.0, "Result could not be saved")


def reset_data():
    resultArea.delete('1.0', END)


# GUI program part
window = Tk(className=' Special Topics in Artificial Intelligence')
window.geometry("1024x600")

# Create a File Explorer label
Label(window, text="Select a .csv file containing Exams", background="white").grid(pady=(8, 4), sticky='e')

filePath = StringVar()
Entry(window, textvariable=filePath, width=36, state='readonly').grid(padx=4, pady=4, row=1, sticky='e')
Button(window, text="Browse", width=16, command=lambda: browse(filePath)).grid(row=1, column=1, sticky='w')

Label(window, text="Number of days in examination session", background="white").grid(row=2, padx=4, pady=4, sticky='e')
Label(window, text="Timeslots per day", background="white").grid(row=3, padx=4, pady=4, sticky='e')
Label(window, text="Time per exam (expressed in hours)", background="white").grid(row=4, padx=4, pady=4, sticky='e')
Label(window, text="Exams starting hour", background="white").grid(row=5, padx=4, pady=4, sticky='e')

# Number of days
entry1 = Entry(window, width=8)

# Number of time slots
entry2 = Entry(window, width=8)

# Time per exam
entry3 = Entry(window, width=8)

# Starting hour
entry4 = Entry(window, width=8)

# Populate the most commonly used values
entry3.insert(0, '2')
entry4.insert(0, '8')

entry1.grid(row=2, column=1, sticky='w')
entry2.grid(row=3, column=1, sticky='w')
entry3.grid(row=4, column=1, sticky='w')
entry4.grid(row=5, column=1, sticky='w')

Button(window, text='Generate Schedule', width=16,
       command=lambda: generate_examination_schedule(entry1, entry2, entry3, entry4, filePath.get())).grid(row=6,
                                                                                                           sticky='e',
                                                                                                           padx=4,
                                                                                                           pady=6)
Button(window, text="Clear Result", width=16, command=reset_data).grid(row=6, column=1, padx=4, pady=6, sticky='w')

# prevent user from typing in the text area
resultArea = ScrolledText(window, width=125, height=21)
resultArea.grid(row=7, columnspan=2)

Button(window, text="Save Schedule", width=16, command=save_schedule).grid(row=8, columnspan=2, pady=8)

window.mainloop()
