string = ""
for i in range(9):
    string += "{"
    for j in range(9):
        string += "{"
        for k in range(9):
            if k == 8:
                string += str(k + 9*j + 81*i)
                if j != 8:
                    string += "}, "
                else:
                    string += "}"
            else:
                string += str(k + 9*j + 81*i)
                string += ", "
    if i != 8:
        string += '},\n'
    else:
        string += '}'

print(string)