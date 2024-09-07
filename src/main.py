import ast
import random
import re
import os
import os.path
from pysat.formula import CNF
from pysat.solvers import Solver
from prettytable import PrettyTable
attribute_dictionary = {}
constraints = {}
Total_values_counter = 0
Number_of_attributes = 0
Name_of_attributes = []
List_of_attributes = []
List_of_Names = []
Penalty = []
QCL = []
Field_names = []
Table_Penalty = PrettyTable()
Table_QCL = PrettyTable()

#def read_lines(worldfilepath): reads in the attributes and sepertes them into a attribute_dictionary
def read_lines(worldfilepath):
    global Number_of_attributes
    global Total_values_counter
    with open(worldfilepath, "r") as f:
        lines = f.readlines()
        lines = [line.rstrip('\n') for line in lines]
    temp_value = 0
    one = int(1)
    Number = 1
    for item in lines:
        attribute = item.split(': ')
        First_attribute = attribute[0]
        Name_of_attributes.append(attribute[0])
        Number_of_attributes = Number_of_attributes+1
        First = str(attribute[1])
        Value=re.split(', ',First)
        Temp = Value[0]
        Temp2 = Value[1]
        Opposite = Number * -1
        List_of_attributes.append([Number,Opposite])
        attribute_dictionary[temp_value]={str(First_attribute):{str(Temp): Number, str(Temp2):Opposite}}
        List_of_Names.append([Temp,Temp2])
        temp_value+=1
        Number +=1
    List = str(List_of_attributes)
    Total_values_counter = 2**Number_of_attributes

# def Binary(Num): calculate the binary values of the row
def Binary(Num):
    String = ''
    number = bin(Num).replace("0b", "")
    if(len(number)<Number_of_attributes):
        length = len(number)
        while length < Number_of_attributes:
            String +='0'
            length+=1
    String+=number
    return String

#def table_cnf(List,attributes): uses PySAT to find the models.
def table_cnf(List,attributes):
    temp_counter = 0
    list_of_attributes = str(attributes)
    Full_list = eval(list_of_attributes)
    String = List.copy()
    for item in attributes:
        m_list = []
        String.append(item)
    cnf = CNF(from_clauses=String)
    with Solver(bootstrap_with=cnf) as solver:
        for m in sorted(solver.enum_models()):
            temp_counter+=1
            m_list.append(m)
    return m_list

#def encoding(): encodes the attributes
def encoding():
    temp_value=0
    temp = 0
    two = 2
    for item in range(Total_values_counter):
        print("\no" + str(item), "–", end='')
        String = Binary(item)
        length = len(String)
        for i in range(length):
            number = int(String[i])
            if(number ==0):
                total = 1
            if (number==1):
                total =0
            print(List_of_Names[i][total],end='')
            if(i!=length-1):
                print(",",end=' ')
    print("\n")

#def hard_constrains(worldfilepath): involves the hard_constraints.txt provided through input.
def hard_constrains(worldfilepath):
    H_List = []
    individual = []
    String = str
    with open(worldfilepath, "r") as f:
        lines = f.readlines()
        lines = [line.rstrip('\n') for line in lines]
    for item in lines:
        String = item
        Split_up=String.split()
        length = len(Split_up)
        counter = 0
        while counter < length-1:
            if Split_up[counter]=='NOT':
                for item in attribute_dictionary:
                    String = Split_up[counter+1]
                    if String in attribute_dictionary[item][Name_of_attributes[item]]:
                        value = attribute_dictionary[item][Name_of_attributes[item]][String]*-1
                        individual.append(value)
                        counter = counter + 2
                        break
            if counter == length:
                H_List.append(individual.copy())
                individual.clear()
                break
            if Split_up[counter]=='OR':
                counter = counter + 1
            if Split_up[counter] =='AND':
                H_List.append(individual.copy())
                individual.clear()
                counter = counter+1
            if Split_up[counter]!='OR' and Split_up[counter]!='AND' and Split_up[counter]!= 'NOT':
                for item in attribute_dictionary:
                    String = Split_up[counter]
                    if String in attribute_dictionary[item][Name_of_attributes[item]]:
                        value = attribute_dictionary[item][Name_of_attributes[item]][String]
                        individual.append(value)
                        counter = counter+1
                        break
            if counter == length:
                H_List.append(individual)
                break
    return H_List

#def penalty(String): is used to process penaltylogic
def penalty(String):
   H_List = []
   individual = []
   Field = String.split(",")
   Field_names.append(Field[0])
   String = String.replace(",", "")
   Split_up = String.split()
   length = len(Split_up)
   counter = 0
   while counter < length:
       if Split_up[counter] == 'NOT':
           for item in attribute_dictionary:
               String = Split_up[counter + 1]
               if String in attribute_dictionary[item][Name_of_attributes[item]]:
                   value = attribute_dictionary[item][Name_of_attributes[item]][String] * -1
                   individual.append(value)
                   counter = counter + 2
                   break
       if counter == length:
           H_List.append(individual.copy())
           individual.clear()
           break
       if Split_up[counter] == 'OR':
           counter = counter + 1
       if Split_up[counter] == 'AND':
           H_List.append(individual.copy())
           individual.clear()
           counter = counter + 1
       if Split_up[counter].isdigit() == True:
           if individual is not None:
               H_List.append(individual.copy())
               individual.clear()
           Penalty.append(int(Split_up[counter]))
           counter = counter + 1
           return H_List
           break
       if Split_up[counter] != 'OR' and Split_up[counter] != 'AND' and Split_up[counter] != 'NOT':
           for item in attribute_dictionary:
               String = Split_up[counter]
               if String in attribute_dictionary[item][Name_of_attributes[item]]:
                   value = attribute_dictionary[item][Name_of_attributes[item]][String]
                   individual.append(value)
                   counter = counter + 1
                   break
       if counter == length:
           H_List.append(individual)
           break
   return H_List

def Penalty_Before(lines):
    Table_Penalty.clear()
    Table_Penalty.clear_rows()
    Field_names.clear()
    Field_names.append("encoding")
    Temp_List = []
    table_List = []
    numbers = []
    count = 0
    Temp_value = 0
    for i in constraints.keys():
        table_List.append("o" + str(i))
        for item in lines:
            Temp_List.clear()
            String = item
            List2 = penalty(String)
            for number in range(Number_of_attributes):
                con = [constraints[i][number]]
                Temp_List.append(con)
            value = table_cnf(List2, Temp_List.copy())
            if not value:
                table_List.append(Penalty[Temp_value])
                numbers.append(Penalty[Temp_value])
                Temp_value = Temp_value + 1
            else:
                table_List.append(0)
                numbers.append(0)
                Temp_value = Temp_value + 1
        if count == 0:
            Field_names.append('Total penalty')
            Table_Penalty.field_names = Field_names
            count = count+1
        Total = sum(numbers.copy())
        table_List.append(Total)
        Table_Penalty.add_row(table_List.copy())
        table_List.clear()
        numbers.clear()

def QCL_Before(lines):
    table_List = []
    Field_QCL = []
    Temp_value = 0
    Table_QCL.clear()
    Table_QCL.clear_rows()
    Field_QCL.append("encoding")
    count = 0
    for i in constraints.keys():
        table_List.append("o" + str(i))
        for item in lines:
            numbers = 10
            array = []
            Temp_List = []
            Field_QCL.append(item)
            Temp_List.clear()
            String = item
            String = String.split()
            Copy = String.copy()
            length = len(String)
            custom_length = 0
            counter = 0
            part = item
            for value in Copy:
                if (value =="BT" or value =="IF"):
                    Copy.remove(value)
            custom_length = len(Copy)
            while counter <custom_length:
                if " IF" in part:
                    if "IF" == String[length - 1]:  # this means that IF is the last statement, it should insert a 0 into the array.
                        array.append(0)
                        split_line = part.split(" IF")
                        part = split_line[0]
                    else:
                        custom_length = custom_length-1
                        numbers = 2
                        split_line = part.split(" IF ")
                        Split = split_line[1]
                        part = split_line[0]
                if numbers!=2:
                    if "IF" and "BT" not in part:
                        Split = part
                        counter = counter + 1
                    if " BT " in part:
                        counter = counter + 1
                        split_line = part.split(" BT ")
                        part = split_line[1]
                        Split = split_line[0]
                List2 = penalty(Split)
                for number in range(Number_of_attributes):
                    con = [constraints[i][number]]
                    Temp_List.append(con)
                value = table_cnf(List2, Temp_List.copy())
                Temp_List.clear()
                if not value:
                    if numbers == 2:
                        array.append(len(String) * 2)
                    else:
                        array.append(0)
                        Temp_value = Temp_value + 1
                    numbers = 10
                else:
                    if numbers == 2:
                        array.append(len(String))
                    else:
                        array.append(counter)
                    numbers = 10
            if array[0]==len(String):
                numbers =100
                if sum(array)==len(String):
                    table_List.append("inf")
                else:
                    if array[0] == len(String):
                        array.pop(0)
                    while len(array)!=0:
                        if array[0] == 0:
                            array.pop(0)
                            array = sorted(array)
                        else:
                            break
                    table_List.append(array[0])
            if array[0]==len(String)*2:
                numbers = 100
                table_List.append("inf")
            while len(array)!=0 and numbers!=100:
                numbers = 70
                if array[0] == 0:
                    array.pop(0)
                    array = sorted(array)
                else:
                    break
            if numbers ==70 and len(array)!=0:
                table_List.append(array[0])
            else:
                if len(array)==0:
                    table_List.append(0)
        if count == 0:
            Table_QCL.field_names = Field_QCL
            count = count+1
        Table_QCL.add_row(table_List)
        table_List.clear()
def feasible():
    if len(constraints)>0:
        print("Yes, there are",len(constraints),"feasible objects")
    else:
        print("No, there are 0 feasible objects")

def preference_logic():
    print("Choose the preference logic to use:")
    print("1. Penalty Logic ")
    print("2. Qualitative Choice Logic")
    print("3. Exit")
    Test = input("Your Choice: ")
    if Test == "1":
        preference_logic2(Test)
    if Test =="2":
        preference_logic2(Test)
    if Test =="3":
        print("Bye!")
        exit()
    else:
        print("Wrong Choice!")
        preference_logic()

def preference_logic2(results):
    #1. Penalty Logic
    if int(results) == 1:
        penaltyvalue = input_call(3)
        with open(penaltyvalue, "r") as f:
            lines = f.readlines()
            lines = [line.rstrip('\n') for line in lines]
        Penalty_Before(lines)
        options_Pen()
    #2. Qualitative Choice Logic
    if int(results)==2:
        QCLvalue = input_call(4)
        with open(QCLvalue, "r") as f:
            lines2 = f.readlines()
            lines2 = [line.rstrip('\n') for line in lines2]
        QCL_Before(lines2)
        options_QCL()
    if int(results) ==3:
        preference_logic()

def options_Pen():
    print("Choose the reasoning task to perform:")
    print("1. Encoding")
    print("2. Feasibility Checking")
    print("3. Show the Table")
    print("4. Exemplification")
    print("5. Omni-optimization")
    print("6. Back to previous menu")
    value = input("Your Choice: ")
    if value != "1" and value != "2" and value != "3" and value != "4" and value != "5" and value != "6":
        print("Please enter a valid number")
        options_Pen()
    else:
        if value =='1':
            encoding()
            print('\n')
            options_Pen()
        if value=="2":
            feasible()
            options_Pen()
        if value =="3":
            print("\n")
            print(Table_Penalty)
            options_Pen()
        if value =="4":
            compare_P()
            options_Pen()
        if value =="5":
            optimization_P()
            options_Pen()
        if value =="6":
            preference_logic()
            options_Pen()
def options_QCL():
    print("Choose the reasoning task to perform:")
    print("1. Encoding")
    print("2. Feasibility Checking")
    print("3. Show the Table")
    print("4. Exemplification")
    print("5. Omni-optimization")
    print("6. Back to previous menu")
    value = input("Your Choice: ")
    if value != "1" and value != "2" and value != "3" and value != "4" and value != "5" and value != "6":
        print("Please enter a valid number")
        options_QCL()
    else:
        if value =="1":
            encoding()
            options_QCL()
        if value=="2":
            feasible()
            options_QCL()
        if value =="3":
            print("\n")
            print(Table_QCL)
            options_QCL()
        if value =="4":
            compare_QCL()
            options_QCL()
        if value =="5":
            optimization_QCL()
            options_QCL()
        if value =="6":
            preference_logic()
            options_QCL()
def optimization_P():
    List = list(constraints.keys())
    length = int(len(Table_Penalty.field_names))
    Low = 90000000000000000000000000
    length2 = int(len(Table_Penalty.rows))
    for i in range(0,length2):
        array = []
        for item in range (1,length):
            value = Table_Penalty.rows[i][length-1]
            if value<Low:
                Low = value
    Opt = []
    for i in range(0,length2):
        if Table_Penalty.rows[i][length-1] == Low:
            Temp = Table_Penalty.rows[i][length-1]
            Opt.append(Table_Penalty.rows[i][0])
    print("All optimal objects: ",end='')
    for i in range(0,len(Opt)):
        if i == len(Opt)-1:
            print(Opt[i])
            break
        else:
            print(Opt[i] + ", ", end='')

def optimization_QCL():
    List = list(constraints.keys())
    Full = []
    length = int(len(Table_QCL.field_names))
    Low = length*2
    length2 = int(len(Table_QCL.rows))
    for i in range(0,length2):
        array = []
        for item in range (1,length):
            if Table_QCL.rows[i][item] == "inf":
                array.append(0)
            else:
                value = Table_QCL.rows[i][item]
                array.append(value)
        Total = sum(array)
        Full.append(Total)
        if Total<Low:
            Low = Total
    Opt = []
    length_two = len(Full)
    for i in range(0,length_two):
        if Full[i] == Low:
            Temp = Table_QCL.rows[i][0]
            Opt.append(Temp)
    print("All optimal objects: ",end='')
    for i in range(0,len(Opt)):
        if i == len(Opt)-1:
            print(Opt[i])
            break
        else:
            print(Opt[i] + ", ", end='')


def compare_P():
    List = list(constraints.keys())
    R = random.sample(List,2)
    option1 = "o" + str(R[0])
    option2 = "o" + str(R[1])
    row1 = 0
    row2 = 0
    length = int(len(Table_Penalty.field_names))
    length2 = int(len(Table_Penalty.rows))
    for i in range(0,length2):
        if Table_Penalty.rows[i][0] == option1:
            row1 = i
        if Table_Penalty.rows[i][0] == option2:
            row2 = i
    obj1 = Table_Penalty.rows[row1][length-1]
    obj2 = Table_Penalty.rows[row2][length-1]
    print("Two randomly selected feasible objects are "+option1+" and "+option2+",and ",end='')
    if obj1>obj2:
        print(option2+" is strictly preferred over "+option1)
    if obj2>obj1:
        print(option1+" is strictly preferred over "+option2)
    if obj1==obj2:
        print(option1+" is equivalent to "+option2)

def compare_QCL():
    List = list(constraints.keys())
    R = random.sample(List,2)
    option1 = "o" + str(R[0])
    option2 = "o" + str(R[1])
    row1 = 0
    row2 = 0
    length = int(len(Table_QCL.field_names))
    length2 = int(len(Table_QCL.rows))
    for i in range(0,length2):
        if Table_QCL.rows[i][0] == option1:
            row1 = i
        if Table_QCL.rows[i][0] == option2:
            row2 = i
    temp = strict(row1,row2,length)
    temp2 = strict(row2,row1,length)
    print("Two randomly selected feasible objects are "+option1+" and "+option2+",and ",end='')
    if temp == 0:
        print(option1+" is strictly preferred over "+option2)
    else:
        if temp2 ==0:
            print(option2+" is strictly preferred over "+option1)
    temp3 =incomparable(row1,row2,length)
    if temp3 == 1:
        print(option1+" and "+option2+" are incomparable")
    temp4 = equivalince(row1,row2,length)
    if temp4 == 0:
        print(option1+" and "+option2+" are equivalent")

def strict(row1,row2,length):
    ST = 0
    for i in range(1,length):
        obj1 = Table_QCL.rows[row1][i]
        obj2 = Table_QCL.rows[row2][i]
        if obj1 == "inf" or obj2 =="inf":
            if obj1=="inf" and obj2!="inf":
                ST = ST+1
            if obj2 =="inf" and obj1 =="inf":
                ST = ST+0
            if obj1 != "inf" and obj2 =="inf":
                ST = ST+0
        else:
            if obj1>obj2:
                ST = ST+1
            if obj1<=obj2:
                ST = ST+0
    return ST
def incomparable(row1,row2,length):
    less =0   #obj<obj2
    more = 0  #obj>obj2
    for i in range(1,length):
        obj1 = Table_QCL.rows[row1][i]
        obj2 = Table_QCL.rows[row2][i]
        if obj1 == "inf" or obj2 =="inf":
            if obj1=="inf" and obj2!="inf": #obj2 does not equal infinite meaning obj1>obj2
                more = more+1
            if obj2 =="inf" and obj1 =="inf": #both are equal
                more = more+0
            if obj1 != "inf" and obj2 =="inf":  #obj1<obj2
                less = less+1
        else:
            if obj1 > obj2:
                more = more+1
            if obj1 < obj2:
                less = less+1
    if(less>0 and more>0):
        return 1   #meaning it is incomparable
    else:
        return 0 #meaning it is not incomparable
def equivalince(row1,row2,length):
    equal = 0
    for i in range(1,length):
        obj1 = Table_QCL.rows[row1][i]
        obj2 = Table_QCL.rows[row2][i]
        if obj1== obj2:
            equal = equal +0
        else:
            equal = equal+1
    if equal!=0:
        return 1
    if equal == 0:
        return 0

def input_call(number):
    if number ==1:
        Test = input("Enter Attributes File Name: ")
    elif number ==2:
        Test = input("Enter Hard Constraints File Name: ")
    elif number ==3:
        Test = input("Enter Preferences File Name: ")
    elif number ==4:
        Test = input("Enter Preferences File Name: ")
    file1 = os.path.isfile(Test)
    if file1 ==True:
        if pass_file(Test,number) == 0:
            print("Please enter valid file")
            return input_call(number)
        else:
            return Test
    else:
        print("Please enter valid file")
        return input_call(number)

def pass_file(worldfilepath,number):
    with open(worldfilepath, "r") as f:
        lines = f.readlines()
    if number ==1:  #checking for attributes
        symbol = ':'
        if symbol in lines[0]:
            return
        else:
            return 0
    elif number ==2: #hard constraints
        symbol = ':'
        if symbol in lines[0]:
            return 0
        for character in lines[0]:
            if character.isdigit():
                return 0
        if " BT " in lines[0].upper() or "IF" in lines[0].upper():
            return 0
        return
    elif number == 3: #penaltylogic.txt
        for character in lines[0]:
            if character.isdigit():
                return
        return 0
    elif number == 4: #qualitativechoicelogic.txt
        if " BT " in lines[0].upper() or "IF" in lines[0].upper():
            return
        else:
            return 0
if __name__ == '__main__':
    print("Welcome to PrefAgent!")
    Lines = input_call(1)
    attributes = read_lines(Lines)
    constraints_values = input_call(2)
    empty = []
    All=table_cnf(empty,List_of_attributes)
    constraints_List = hard_constrains(constraints_values)
    constraint_results = table_cnf(constraints_List,List_of_attributes)
    for item in constraint_results:
        Temp_counter = 0
        for i in All:
            if item == i:
                constraints[Temp_counter] = item
                break
            else:
                Temp_counter = Temp_counter+1
    preference_logic()