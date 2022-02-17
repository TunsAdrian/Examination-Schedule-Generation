from z3 import *
import csv
import tabulate
import tkinter
from tkinter import *
from tkinter import filedialog
from tkinter.messagebox import showinfo
import os



def browse():
    global fileName
    filename = filedialog.askopenfilename(initialdir="/",
                                          title="Select a File",
                                          filetypes=(("Text files",
                                                      "*.csv*"),
                                                     ("all files",
                                                      "*.*")), )

    label_file_explorer.configure(text="File Opened: " + filename)
    fileName = filename
    return fileName


def generate_examination_schedule():
    coursesDict = {}
    slotDict = {}

    timePerExam = int(e1.get())
    examsStartingHour = int(e2.get())
    numberOfTimeSlots = int(e3.get())
    numberOfDays = int(e4.get())

    def validate_input(input_data):
        if input_data.find('/') != -1 or input_data.find('~') != -1:
            raise Exception("Input data can't contain the following characters: '/' '~'")


    # TODO: replace with file containing all exams
    with open(fileName, 'r') as file:
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
        txtarea.insert(END, tabulate.tabulate(finalSchedule, headers="firstrow", tablefmt="fancy_grid"))

    else:
        print("---A proper schedule could not be generated for the input data---")
    with open('exams-schedule.txt', 'w') as file:
        file.write(tabulate.tabulate(finalSchedule,headers="firstrow", tablefmt="fancy_grid"))

def deleteFile():
    if os.path.exists("exams-schedule.txt"):
        os.remove("exams-schedule.txt")
    else:
        print("The file does not exist")
    txtarea.delete('1.0', END)

window = Tk()

window.title('STAI')

window.geometry("1500x1200")

window.config(background="white")

# Create a File Explorer label
label_file_explorer = Label(window,
                            text="STAI Project",
                            width=50, height=2,
                            fg="blue")

button_explore = Button(window,
                        text="Browse Files",
                        command=browse)

button_exit = Button(window,
                     text="Exit",
                     command=exit)

label_file_explorer.grid(column=1, row=1)

button_explore.grid(column=1, row=2)


tkinter.Label(window,text="Number of days").grid(row=3)
tkinter.Label(window,text="Time slots per day").grid(row=4)
tkinter.Label(window,text="Time per exam").grid(row=5)
tkinter.Label(window,text="Starting hour").grid(row=6)


e1 = tkinter.Entry(window)
e2 = tkinter.Entry(window)
e3 = tkinter.Entry(window)
e4 = tkinter.Entry(window)


e1.grid(row=3, column=1)
e2.grid(row=4, column=1)
e3.grid(row=5, column=1)
e4.grid(row=6, column=1)


tkinter.Button(window, text='Send data', command=generate_examination_schedule).grid(row=7)
txtarea = Text(window, width=140, height=20)
txtarea.grid(pady=20)

tkinter.Button(window, text="Save output").grid(row=14)
tkinter.Button(window, text="Delete file", command = deleteFile).grid(row=15)

button_exit.grid(column=1, row=17)
window.mainloop()

# TODO: take from GUI

###


# TODO: use in GUI for generating file with schedule